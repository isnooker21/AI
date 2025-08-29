import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox
import MetaTrader5 as mt5
import pandas as pd
import numpy as np
from datetime import datetime, timedelta
import threading
import time
import json
import logging
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple
from enum import Enum
import queue
import os
import pickle

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

@dataclass
class Signal:
    """Signal data structure"""
    timestamp: datetime
    symbol: str
    direction: str  # 'BUY' or 'SELL'
    strength: float  # 0.5 - 3.0
    reason: str
    price: float

@dataclass
class Position:
    """Position data structure"""
    ticket: int
    symbol: str
    type: str
    volume: float
    open_price: float
    current_price: float
    profit: float
    profit_per_lot: float
    role: str  # MAIN, HG, SUPPORT, SACRIFICE
    efficiency: str  # excellent, good, fair, poor

class OrderRole(Enum):
    MAIN = "MAIN"
    HEDGE_GUARD = "HG"
    SUPPORT = "SUPPORT"
    SACRIFICE = "SACRIFICE"

class TradingSystem:
    def __init__(self):
        self.mt5_connected = False
        self.trading_active = False
        self.symbol = "XAUUSD.v"  # เปลี่ยนจาก "XAUUSD" เป็น "XAUUSD.v"
        self.base_lot = 0.01
        self.max_positions = 50
        self.max_daily_trades = 100
        self.min_margin_level = 200.0
        self.signal_cooldown = 60  # seconds
        self.max_signals_per_hour = 40
        
        # Trading statistics
        self.daily_trades = 0
        self.total_signals = 0
        self.successful_signals = 0
        self.last_signal_time = None
        self.hourly_signals = []
        
        # Portfolio tracking
        self.positions: List[Position] = []
        self.buy_volume = 0.0
        self.sell_volume = 0.0
        self.portfolio_health = 100.0
        
        # GUI components
        self.root = None
        self.log_queue = queue.Queue()
        
        # 🧠 Smart Signal Router & Position Management
        self.position_tracker = {}
        self.smart_router_enabled = True
        self.balance_target_ratio = 0.5
        self.balance_tolerance = 0.15  # ยอมรับ 35:65 - 65:35
        self.redirect_threshold = 0.65  # redirect เมื่อ balance เกิน 65:35
        self.max_redirect_ratio = 0.4   # redirect ได้สูงสุด 40% ของ signals
        
        # Adaptive profit management
        self.profit_harvest_threshold = 50.0
        self.adaptive_profit_targets = True
        self.min_profit_for_redirect_close = 25.0
        self.position_efficiency_check_interval = 30
        self.last_efficiency_check = None
        
        # Smart routing statistics
        self.total_redirects = 0
        self.successful_redirects = 0
        self.redirect_profit_captured = 0.0
        self.last_redirect_time = None
        self.redirect_cooldown = 30  # วินาที
        
        # Position hold scoring
        self.max_hold_hours = 48
        self.gentle_management = True
        self.emergency_mode_threshold = 25  # portfolio health

        # Auto-detect filling type
        self.filling_type = None
        self.filling_types_priority = [
            mt5.ORDER_FILLING_IOC,  # Immediate or Cancel
            mt5.ORDER_FILLING_FOK,  # Fill or Kill  
            mt5.ORDER_FILLING_RETURN  # Return (default)
        ]

        # 🛡️ Anti-Exposure Protection System
        self.anti_exposure_enabled = True
        self.max_exposure_distance = 150  # pips (1.5 points for XAUUSD)
        self.exposure_warning_distance = 100  # pips
        self.auto_hedge_enabled = True
        self.hedge_trigger_distance = 120  # pips
        
        # 🎯 Support/Resistance Detection
        self.sr_detection_enabled = True
        self.sr_lookback_periods = 50  # candles to analyze
        self.sr_strength_threshold = 3  # minimum touches to confirm S/R
        self.sr_proximity_pips = 20  # pips distance to consider "at" S/R
        
        # 🔄 Auto-Hedge System - ENHANCED
        self.hedge_system_enabled = True
        self.hedge_calculation_method = "LOSS_COVERAGE"  # VOLUME_MATCH, LOSS_COVERAGE, DISTANCE_BASED
        self.hedge_coverage_ratio = 1.2  # 120% loss coverage
        self.min_hedge_volume = 0.01
        self.max_hedge_volume = 5.0
        self.hedge_distance_multiplier = 1.5
        
        # 🛠️ Advanced Drawdown Management (NEW)
        self.drawdown_management_enabled = True
        self.drawdown_trigger_pips = 150  # เริ่มคิดหาทางแก้ที่ 150 pips
        self.critical_drawdown_pips = 250  # ถือว่าวิกฤตที่ 250 pips
        self.emergency_drawdown_pips = 350  # ต้องแก้ทันทีที่ 350 pips
        
        # 🎯 Dynamic Hedge Strategy
        self.hedge_strategy = "SMART_RECOVERY"  # IMMEDIATE, SMART_RECOVERY, AVERAGING, HYBRID
        self.hedge_volume_calculation = "DYNAMIC_RATIO"  # FIXED_RATIO, DYNAMIC_RATIO, LOSS_BASED
        self.hedge_min_profit_to_close = 0.5  # 0.5% profit ถึงจะปิด hedge
        self.hedge_recovery_target = 2.0  # เป้า 2% กำไรรวม
        
        # 🔄 Multi-Level Hedge System
        self.max_hedge_levels = 3  # สูงสุด 3 ระดับ hedge
        self.hedge_distance_increment = 50  # เพิ่มระยะห่าง 50 pips ต่อ level
        self.hedge_volume_multiplier = 1.3  # เพิ่ม volume 1.3 เท่าต่อ level
        
        # 📊 Hedge Tracking & Analytics
        self.active_hedges = {}  # {original_ticket: [hedge_tickets]}
        self.hedge_pairs = {}    # {hedge_ticket: original_ticket}
        self.hedge_analytics = {
            'total_hedges_created': 0,
            'successful_recoveries': 0,
            'total_recovery_profit': 0.0,
            'avg_recovery_time_hours': 0.0,
            'hedge_effectiveness': 0.0,
            'active_hedge_pairs': 0
        }

        # 🎯 Smart Pair/Group Closing System (เปลี่ยนเป็น %)
        self.pair_closing_enabled = True
        self.min_pair_profit_percent = 2.0  # กำไรรวมขั้นต่ำ 2%
        self.group_closing_enabled = True
        self.min_group_profit_percent = 3.0  # กำไรรวมขั้นต่ำ 3%
        self.max_loss_percent = -15.0  # ขาดทุนสูงสุด -15% ต่อไม้ที่ยอมให้จับคู่
        self.portfolio_recovery_mode = True
        self.recovery_target_percent = 5.0  # เป้ากำไร 5% สำหรับโหมดฟื้นฟู
        
        # เปลี่ยน profit targets เป็น %
        self.profit_harvest_threshold_percent = 8.0  # 8% กำไรต่อ lot
        self.min_profit_for_redirect_close_percent = 3.0  # 3% ขั้นต่ำสำหรับ redirect
        self.emergency_profit_threshold_percent = 4.0  # 4% ขั้นต่ำสำหรับ emergency close
        
        # Statistics
        self.total_pair_closes = 0
        self.successful_pair_closes = 0
        self.pair_profit_captured = 0.0
        self.total_group_closes = 0
        self.group_profit_captured = 0.0

        # เพิ่มชื่อไฟล์สำหรับ save/load
        self.state_file = "trading_state.json"
        self.positions_file = "positions_backup.pkl"
        
        # โหลดสถานะเมื่อเริ่มโปรแกรม
        self.load_trading_state()
        
        # 🛠️ Smart HG System - เพิ่มส่วนนี้
        self.smart_hg_enabled = True
        self.hg_intelligence_level = "ADVANCED"
        self.hg_decision_threshold = 75
        self.hg_max_concurrent = 3
        self.hg_cooldown_minutes = 15
        
        # 📊 HG Decision Parameters
        self.market_context_weight = 0.3
        self.position_cluster_analysis = True
        self.dynamic_risk_assessment = True
        self.partial_hedge_enabled = True
        self.hedge_timing_optimization = True
        
        # 🎯 Advanced HG Strategies
        self.hg_strategy_selection = "AUTO_ADAPTIVE"
        self.min_loss_threshold_for_hg = 100
        self.max_portfolio_hg_ratio = 0.4
        
        # 💡 Pattern Recognition
        self.hg_pattern_learning = True
        self.avoid_bad_timing = True
        self.market_reversal_detection = True
        self.hg_performance_history = []
        self.hg_success_patterns = {}
        self.hg_failure_analysis = {}
        
        # 🔧 Missing Variables - Added for complete initialization
        self.last_hedge_time = None  # Track last hedge execution time
        self.recent_volatility = 1.0  # Default volatility level

    def log(self, message: str, level: str = "INFO"):
        """Thread-safe logging"""
        timestamp = datetime.now().strftime("%H:%M:%S")
        log_message = f"[{timestamp}] {level}: {message}"
        self.log_queue.put(log_message)
        
        if level == "ERROR":
            logger.error(message)
        elif level == "WARNING":
            logger.warning(message)
        else:
            logger.info(message)

    def detect_broker_filling_type(self) -> int:
        """Auto-detect broker's supported filling type"""
        if not self.mt5_connected:
            return mt5.ORDER_FILLING_IOC
            
        try:
            # Get symbol info to check filling modes
            symbol_info = mt5.symbol_info(self.symbol)
            if symbol_info is None:
                self.log(f"Cannot get symbol info for {self.symbol}", "WARNING")
                return mt5.ORDER_FILLING_IOC
            
            filling_modes = symbol_info.filling_mode
            
            # Check each filling type in priority order
            for filling_type in self.filling_types_priority:
                if filling_modes & filling_type:
                    filling_name = {
                        mt5.ORDER_FILLING_IOC: "IOC (Immediate or Cancel)",
                        mt5.ORDER_FILLING_FOK: "FOK (Fill or Kill)",
                        mt5.ORDER_FILLING_RETURN: "RETURN (Default)"
                    }.get(filling_type, f"Unknown ({filling_type})")
                    
                    self.log(f"✅ Detected broker filling type: {filling_name}")
                    return filling_type
            
            # Fallback to RETURN if nothing else works
            self.log("⚠️ Using fallback filling type: RETURN", "WARNING")
            return mt5.ORDER_FILLING_RETURN
            
        except Exception as e:
            self.log(f"Error detecting filling type: {str(e)}", "ERROR")
            return mt5.ORDER_FILLING_IOC

    def connect_mt5(self) -> bool:
        """Connect to MetaTrader 5"""
        try:
            if not mt5.initialize():
                self.log("MT5 initialization failed", "ERROR")
                return False
            
            # Get account info
            account_info = mt5.account_info()
            if account_info is None:
                self.log("Failed to get account info", "ERROR")
                return False
            
            self.mt5_connected = True
            
            # Auto-detect filling type after connection
            self.filling_type = self.detect_broker_filling_type()
            
            self.log(f"Connected to MT5 - Account: {account_info.login}")
            self.log(f"Balance: ${account_info.balance:.2f}, Equity: ${account_info.equity:.2f}")
            return True
            
        except Exception as e:
            self.log(f"MT5 connection error: {str(e)}", "ERROR")
            return False

    def disconnect_mt5(self):
        """Disconnect from MetaTrader 5 and save state"""
        if self.trading_active:
            self.trading_active = False
            time.sleep(2)  # รอให้ loop หยุด
        
        if self.mt5_connected:
            # Save state ก่อนปิด
            self.save_trading_state()
            mt5.shutdown()
            self.mt5_connected = False
            self.log("💾 State saved and disconnected from MT5")

    def optimize_trading_parameters(self):
        """ปรับพารามิเตอร์แบบ adaptive"""
        try:
            # วิเคราะห์ performance ล่าสุด
            if self.total_signals >= 20:  # มีข้อมูลพอ
                success_rate = self.successful_signals / self.total_signals
                
                # ปรับ signal cooldown
                if success_rate > 0.8:
                    self.signal_cooldown = max(30, self.signal_cooldown - 5)  # เร็วขึ้น
                elif success_rate < 0.5:
                    self.signal_cooldown = min(120, self.signal_cooldown + 10)  # ช้าลง
                
                # ปรับ profit targets
                avg_profit = self.redirect_profit_captured / max(1, self.successful_redirects)
                if avg_profit > 50:
                    self.profit_harvest_threshold_percent *= 1.1  # เป้าสูงขึ้น
                elif avg_profit < 20:
                    self.profit_harvest_threshold_percent *= 0.9  # เป้าต่ำลง
                
                self.log(f"🎛️ Parameters optimized: Success rate {success_rate:.1%}")
                
        except Exception as e:
            self.log(f"Error optimizing parameters: {str(e)}", "ERROR")

    def enhanced_risk_management(self):
        """การจัดการความเสี่ยงขั้นสูง"""
        try:
            account_info = mt5.account_info()
            if not account_info:
                return
            
            # 1. Dynamic position size based on account equity
            equity = account_info.equity
            if equity < 1000:
                self.base_lot = 0.01
            elif equity < 5000:
                self.base_lot = 0.02
            elif equity < 10000:
                self.base_lot = 0.03
            else:
                self.base_lot = min(0.05, equity / 200000)  # Max 0.05 lots
            
            # 2. Drawdown protection
            balance = account_info.balance
            current_drawdown = (balance - equity) / balance * 100 if balance > 0 else 0
            
            if current_drawdown > 20:  # 20% drawdown
                self.trading_active = False
                self.log("🚨 EMERGENCY STOP: 20% drawdown reached", "ERROR")
            elif current_drawdown > 10:  # 10% drawdown - reduce activity
                self.max_signals_per_hour = 20
                self.signal_cooldown = 120
                self.log("⚠️ Risk mode: Reduced trading activity", "WARNING")
            
            # 3. Margin level protection
            if account_info.margin > 0:
                margin_level = (equity / account_info.margin) * 100
                if margin_level < 150:
                    self.gentle_management = False  # Aggressive closing
                    self.log("⚠️ Low margin: Activating aggressive management", "WARNING")
                
        except Exception as e:
            self.log(f"Error in risk management: {str(e)}", "ERROR")

    def calculate_market_volatility(self, df: pd.DataFrame) -> float:
        """Calculate recent market volatility"""
        if df is None or len(df) < 5:
            return 1.0
            
        try:
            # คำนวณ ATR (Average True Range) แบบง่าย
            df['tr1'] = df['high'] - df['low']
            df['tr2'] = abs(df['high'] - df['close'].shift(1))
            df['tr3'] = abs(df['low'] - df['close'].shift(1))
            df['true_range'] = df[['tr1', 'tr2', 'tr3']].max(axis=1)
            
            # ATR ช่วง 5 periods
            atr = df['true_range'].tail(5).mean()
            
            # Normalize ATR (สำหรับ XAUUSD)
            volatility = atr / 10.0  # ปรับค่าให้เหมาะสม
            
            return max(0.2, min(5.0, volatility))
            
        except Exception as e:
            self.log(f"Error calculating volatility: {str(e)}", "ERROR")
            return 1.0

    def get_market_data(self) -> Optional[pd.DataFrame]:
        """Get recent market data for analysis"""
        if not self.mt5_connected:
            return None
            
        try:
            # Get last 15 M5 candles (เพิ่มจาก 10)
            rates = mt5.copy_rates_from_pos(self.symbol, mt5.TIMEFRAME_M5, 0, 15)
            if rates is None or len(rates) < 5:
                return None
                
            df = pd.DataFrame(rates)
            df['time'] = pd.to_datetime(df['time'], unit='s')
            
            # Calculate candle properties
            df['body'] = abs(df['close'] - df['open'])
            df['total_range'] = df['high'] - df['low']
            df['body_ratio'] = df['body'] / df['total_range'] * 100
            df['is_green'] = df['close'] > df['open']
            df['movement'] = abs(df['close'] - df['open'])
            
            # คำนวณและเก็บ volatility
            self.recent_volatility = self.calculate_market_volatility(df)
            
            return df
            
        except Exception as e:
            self.log(f"Error getting market data: {str(e)}", "ERROR")
            return None

    def analyze_volume_pattern(self, df: pd.DataFrame) -> dict:
        """📊 วิเคราะห์รูปแบบปริมาณการซื้อขาย"""
        try:
            if df is None or len(df) < 5:
                return {'pattern': 'INSUFFICIENT_DATA', 'strength': 0.0, 'trend': 'NEUTRAL'}
            
            # คำนวณ volume indicators
            recent_volume = df['tick_volume'].tail(5).mean()
            avg_volume = df['tick_volume'].mean() if len(df) > 10 else recent_volume
            
            # วิเคราะห์รูปแบบ volume
            volume_trend = 'INCREASING' if recent_volume > avg_volume * 1.2 else 'DECREASING' if recent_volume < avg_volume * 0.8 else 'STABLE'
            
            # คำนวณความแรงของ pattern
            strength = min(1.0, abs(recent_volume - avg_volume) / avg_volume)
            
            return {
                'pattern': f'VOLUME_{volume_trend}',
                'strength': strength,
                'trend': volume_trend,
                'recent_avg': recent_volume,
                'historical_avg': avg_volume
            }
            
        except Exception as e:
            self.log(f"Error analyzing volume pattern: {str(e)}", "ERROR")
            return {'pattern': 'ERROR', 'strength': 0.0, 'trend': 'NEUTRAL'}

    def detect_sr_levels(self, df: pd.DataFrame) -> dict:
        """🎯 ตรวจหา Support/Resistance levels"""
        try:
            if df is None or len(df) < 10:
                return {'support_levels': [], 'resistance_levels': [], 'current_bias': 'NEUTRAL'}
            
            # หา local highs และ lows
            highs = []
            lows = []
            
            for i in range(2, len(df) - 2):
                # Local high
                if (df.iloc[i]['high'] > df.iloc[i-1]['high'] and 
                    df.iloc[i]['high'] > df.iloc[i+1]['high'] and
                    df.iloc[i]['high'] > df.iloc[i-2]['high'] and 
                    df.iloc[i]['high'] > df.iloc[i+2]['high']):
                    highs.append(df.iloc[i]['high'])
                
                # Local low
                if (df.iloc[i]['low'] < df.iloc[i-1]['low'] and 
                    df.iloc[i]['low'] < df.iloc[i+1]['low'] and
                    df.iloc[i]['low'] < df.iloc[i-2]['low'] and 
                    df.iloc[i]['low'] < df.iloc[i+2]['low']):
                    lows.append(df.iloc[i]['low'])
            
            # กรอง levels ที่ใกล้เคียงกัน
            current_price = df.iloc[-1]['close']
            proximity_threshold = 0.5  # 0.5 points for XAUUSD
            
            resistance_levels = []
            support_levels = []
            
            for high in highs:
                if high > current_price and not any(abs(high - r) < proximity_threshold for r in resistance_levels):
                    resistance_levels.append(high)
                    
            for low in lows:
                if low < current_price and not any(abs(low - s) < proximity_threshold for s in support_levels):
                    support_levels.append(low)
            
            # จำกัดจำนวน levels
            resistance_levels = sorted(resistance_levels)[:3]
            support_levels = sorted(support_levels, reverse=True)[:3]
            
            # กำหนด bias
            bias = 'NEUTRAL'
            if resistance_levels and support_levels:
                if len(resistance_levels) > len(support_levels):
                    bias = 'BEARISH'
                elif len(support_levels) > len(resistance_levels):
                    bias = 'BULLISH'
            
            return {
                'support_levels': support_levels,
                'resistance_levels': resistance_levels,
                'current_bias': bias,
                'current_price': current_price
            }
            
        except Exception as e:
            self.log(f"Error detecting S/R levels: {str(e)}", "ERROR")
            return {'support_levels': [], 'resistance_levels': [], 'current_bias': 'NEUTRAL'}

    def calculate_market_sentiment(self, df: pd.DataFrame) -> float:
        """🧠 คำนวณ sentiment ของตลาด (0.0-1.0)"""
        try:
            if df is None or len(df) < 5:
                return 0.5  # Neutral sentiment
            
            sentiment_score = 0.5  # เริ่มต้นที่ neutral
            
            # 1. Price momentum (30% weight)
            recent_close = df.iloc[-1]['close']
            previous_close = df.iloc[-5]['close'] if len(df) >= 5 else df.iloc[0]['close']
            price_change = (recent_close - previous_close) / previous_close
            momentum_score = 0.5 + (price_change * 10)  # Scale to 0-1
            momentum_score = max(0.0, min(1.0, momentum_score))
            
            # 2. Candle patterns (25% weight)
            green_count = df.tail(5)['is_green'].sum()
            pattern_score = green_count / 5.0
            
            # 3. Volume confirmation (20% weight)
            volume_data = self.analyze_volume_pattern(df)
            volume_score = 0.5
            if volume_data['trend'] == 'INCREASING':
                volume_score = 0.7
            elif volume_data['trend'] == 'DECREASING':
                volume_score = 0.3
            
            # 4. Volatility factor (15% weight)
            volatility = self.calculate_market_volatility(df)
            volatility_score = min(1.0, volatility / 2.0)  # Higher volatility = more bullish potential
            
            # 5. Recent body strength (10% weight)
            avg_body_ratio = df.tail(3)['body_ratio'].mean()
            body_score = min(1.0, avg_body_ratio / 10.0)  # Strong bodies = more directional
            
            # Weighted combination
            sentiment_score = (
                momentum_score * 0.30 +
                pattern_score * 0.25 +
                volume_score * 0.20 +
                volatility_score * 0.15 +
                body_score * 0.10
            )
            
            return max(0.0, min(1.0, sentiment_score))
            
        except Exception as e:
            self.log(f"Error calculating market sentiment: {str(e)}", "ERROR")
            return 0.5  # Return neutral on error

    def analyze_real_time_sentiment(self) -> dict:
        """วิเคราะห์ sentiment แบบ real-time"""
        try:
            sentiment = {
                'direction': 'NEUTRAL',
                'strength': 0.5,
                'confidence': 0.5,
                'recommendation': 'HOLD',
                'factors': []
            }
            
            market_data = self.get_market_data()
            if market_data is None:
                return sentiment
            
            # Multi-timeframe analysis
            short_term = market_data.tail(3)  # Last 3 candles
            medium_term = market_data.tail(7)  # Last 7 candles
            
            # Factor 1: Short-term momentum
            short_green_ratio = short_term['is_green'].sum() / 3
            if short_green_ratio >= 0.67:
                sentiment['factors'].append("Short-term bullish momentum")
                sentiment['strength'] += 0.2
            elif short_green_ratio <= 0.33:
                sentiment['factors'].append("Short-term bearish momentum")
                sentiment['strength'] += 0.2
            
            # Factor 2: Medium-term trend
            medium_green_ratio = medium_term['is_green'].sum() / 7
            if medium_green_ratio >= 0.6:
                sentiment['factors'].append("Medium-term uptrend")
                sentiment['strength'] += 0.15
            elif medium_green_ratio <= 0.4:
                sentiment['factors'].append("Medium-term downtrend")
                sentiment['strength'] += 0.15
            
            # Factor 3: Volume/Body analysis
            avg_body_ratio = short_term['body_ratio'].mean()
            if avg_body_ratio > 15:
                sentiment['factors'].append("Strong candle bodies")
                sentiment['confidence'] += 0.2
            
            # Factor 4: Price movement
            avg_movement = short_term['movement'].mean()
            if avg_movement > 0.5:
                sentiment['factors'].append("High price movement")
                sentiment['confidence'] += 0.15
            
            # Determine final direction
            if short_green_ratio > 0.6 and medium_green_ratio > 0.5:
                sentiment['direction'] = 'BULLISH'
                sentiment['recommendation'] = 'BUY_BIAS'
            elif short_green_ratio < 0.4 and medium_green_ratio < 0.5:
                sentiment['direction'] = 'BEARISH'
                sentiment['recommendation'] = 'SELL_BIAS'
            
            # Limit values
            sentiment['strength'] = min(1.0, sentiment['strength'])
            sentiment['confidence'] = min(1.0, sentiment['confidence'])
            
            return sentiment
            
        except Exception as e:
            self.log(f"Error analyzing sentiment: {str(e)}", "ERROR")
            return sentiment

    def analyze_portfolio_exposure(self) -> Dict:
        """🛡️ วิเคราะห์ระดับ exposure ของ portfolio"""
        try:
            analysis = {
                'total_exposure_pips': 0,
                'max_distance_buy': 0,
                'max_distance_sell': 0,
                'exposure_level': 'LOW',
                'needs_hedge': False,
                'recommended_hedge': None,
                'risk_score': 0
            }
            
            if not self.positions:
                return analysis
            
            # ดึงราคาปัจจุบัน
            current_tick = mt5.symbol_info_tick(self.symbol)
            if not current_tick:
                return analysis
            
            current_price = (current_tick.bid + current_tick.ask) / 2
            
            buy_positions = [p for p in self.positions if p.type == "BUY"]
            sell_positions = [p for p in self.positions if p.type == "SELL"]
            
            # คำนวณระยะห่างของ BUY positions
            buy_distances = []
            for pos in buy_positions:
                distance_pips = (current_price - pos.open_price) * 100
                buy_distances.append(distance_pips)
            
            # คำนวณระยะห่างของ SELL positions
            sell_distances = []
            for pos in sell_positions:
                distance_pips = (pos.open_price - current_price) * 100
                sell_distances.append(distance_pips)
            
            # คำนวณค่าต่างๆ
            if buy_distances:
                analysis['max_distance_buy'] = max(buy_distances)
            
            if sell_distances:
                analysis['max_distance_sell'] = max(sell_distances)
            
            # คำนวณ total exposure
            max_buy_distance = abs(analysis['max_distance_buy'])
            max_sell_distance = abs(analysis['max_distance_sell'])
            analysis['total_exposure_pips'] = max_buy_distance + max_sell_distance
            
            # ประเมิน exposure level
            if analysis['total_exposure_pips'] > 300:
                analysis['exposure_level'] = 'CRITICAL'
                analysis['risk_score'] = 90
            elif analysis['total_exposure_pips'] > 200:
                analysis['exposure_level'] = 'HIGH'
                analysis['risk_score'] = 70
            elif analysis['total_exposure_pips'] > 100:
                analysis['exposure_level'] = 'MEDIUM'
                analysis['risk_score'] = 40
            else:
                analysis['exposure_level'] = 'LOW'
                analysis['risk_score'] = 20
            
            # ตรวจสอบว่าต้องการ hedge หรือไม่
            analysis['needs_hedge'] = (
                analysis['total_exposure_pips'] > self.hedge_trigger_distance or
                max_buy_distance > self.max_exposure_distance or
                max_sell_distance > self.max_exposure_distance
            )
            
            return analysis
            
        except Exception as e:
            self.log(f"Error analyzing portfolio exposure: {str(e)}", "ERROR")
            return analysis

    def analyze_mini_trend(self, df: pd.DataFrame) -> Optional[Signal]:
        """Analyze mini trend and generate signals with new conditions"""
        if df is None or len(df) < 3:
            return None
            
        try:
            # Get last 3 candles
            last_3 = df.tail(3)
            current_candle = last_3.iloc[-1]  # แท่งปัจจุบัน
            current_price = current_candle['close']
            
            # Count green/red candles
            green_count = last_3['is_green'].sum()
            red_count = 3 - green_count
            
            # Check minimum requirements
            min_body_ratio = 5.0  # 5%
            min_movement = 0.2    # 0.2 points (20 pips)
            
            # Calculate signal strength based on various factors
            avg_body_ratio = last_3['body_ratio'].mean()
            avg_movement = last_3['movement'].mean()
            
            strength = 1.0
            if avg_body_ratio > 10:
                strength += 0.3
            if avg_movement > 0.5:
                strength += 0.4
            if avg_movement > 1.0:
                strength += 0.3
                
            strength = min(3.0, max(0.5, strength))
            
            # 🟢 BUY signal conditions - NEW LOGIC
            if (green_count >= 2 and 
                avg_body_ratio >= min_body_ratio and 
                avg_movement >= min_movement and
                current_candle['is_green']):  # แท่งปัจจุบันต้องเป็นสีเขียว
                
                return Signal(
                    timestamp=datetime.now(),
                    symbol=self.symbol,
                    direction='BUY',
                    strength=strength,
                    reason=f"🟢 Green {green_count}/3 + Current Green, Body: {avg_body_ratio:.1f}%, Move: {avg_movement:.2f}",
                    price=current_price
                )
            
            # 🔴 SELL signal conditions - NEW LOGIC
            elif (red_count >= 2 and 
                  avg_body_ratio >= min_body_ratio and 
                  avg_movement >= min_movement and
                  not current_candle['is_green']):  # แท่งปัจจุบันต้องเป็นสีแดง
                
                return Signal(
                    timestamp=datetime.now(),
                    symbol=self.symbol,
                    direction='SELL',
                    strength=strength,
                    reason=f"🔴 Red {red_count}/3 + Current Red, Body: {avg_body_ratio:.1f}%, Move: {avg_movement:.2f}",
                    price=current_price
                )
            
            return None
            
        except Exception as e:
            self.log(f"Error analyzing trend: {str(e)}", "ERROR")
            return None

    def analyze_advanced_market_patterns(self, df: pd.DataFrame) -> Optional[Signal]:
        """วิเคราะห์ pattern ขั้นสูงด้วย AI-inspired techniques"""
        if df is None or len(df) < 10:
            return None
        
        try:
            # เพิ่มตัววิเคราะห์ขั้นสูง
            patterns = {
                'trend_strength': self.calculate_trend_strength(df),
                'momentum_score': self.calculate_momentum_score(df),
                'volume_pattern': self.analyze_volume_pattern(df),
                'support_resistance': self.detect_sr_levels(df),
                'market_sentiment': self.calculate_market_sentiment(df)
            }
            
            # AI-inspired scoring
            signal_confidence = self.calculate_ai_confidence(patterns)
            
            if signal_confidence['should_trade']:
                return Signal(
                    timestamp=datetime.now(),
                    symbol=self.symbol,
                    direction=signal_confidence['direction'],
                    strength=signal_confidence['strength'],
                    reason=f"🤖 AI Pattern: {signal_confidence['pattern_name']} (Conf: {signal_confidence['confidence']:.1%})",
                    price=df.iloc[-1]['close']
                )
            
            return None
            
        except Exception as e:
            self.log(f"Error in advanced analysis: {str(e)}", "ERROR")
            return None

    def calculate_trend_strength(self, df: pd.DataFrame) -> float:
        """คำนวณความแรงของ trend"""
        try:
            last_10 = df.tail(10)
            
            # Linear regression slope
            x = np.arange(len(last_10))
            y = last_10['close'].values
            slope = np.polyfit(x, y, 1)[0]
            
            # Normalize slope to 0-1 scale
            price_range = last_10['close'].max() - last_10['close'].min()
            trend_strength = abs(slope) / (price_range / len(last_10)) if price_range > 0 else 0
            
            return min(1.0, trend_strength)
            
        except Exception as e:
            return 0.5

    def calculate_momentum_score(self, df: pd.DataFrame) -> float:
        """คำนวณ momentum ด้วย RSI-inspired method"""
        try:
            last_10 = df.tail(10)
            
            # Calculate price changes
            price_changes = last_10['close'].diff().dropna()
            
            # Separate gains and losses
            gains = price_changes.where(price_changes > 0, 0)
            losses = -price_changes.where(price_changes < 0, 0)
            
            # Calculate average gains and losses
            avg_gain = gains.mean()
            avg_loss = losses.mean()
            
            # RSI-like calculation
            if avg_loss == 0:
                return 1.0
            
            rs = avg_gain / avg_loss
            momentum = rs / (1 + rs)
            
            return momentum
            
        except Exception as e:
            return 0.5

    def calculate_ai_confidence(self, patterns: dict) -> dict:
        """คำนวณความเชื่อมั่นแบบ AI"""
        try:
            confidence_score = 0.0
            direction_votes = {'BUY': 0, 'SELL': 0}
            
            # Trend analysis
            trend_strength = patterns['trend_strength']
            if trend_strength > 0.7:
                confidence_score += 0.3
                direction_votes['BUY'] += trend_strength
            elif trend_strength < 0.3:
                confidence_score += 0.3
                direction_votes['SELL'] += (1 - trend_strength)
            
            # Momentum analysis
            momentum = patterns['momentum_score']
            if momentum > 0.6:
                confidence_score += 0.25
                direction_votes['BUY'] += momentum
            elif momentum < 0.4:
                confidence_score += 0.25
                direction_votes['SELL'] += (1 - momentum)
            
            # Market sentiment
            sentiment = patterns['market_sentiment']
            if abs(sentiment - 0.5) > 0.2:
                confidence_score += 0.2
                if sentiment > 0.5:
                    direction_votes['BUY'] += sentiment
                else:
                    direction_votes['SELL'] += (1 - sentiment)
            
            # Pattern recognition bonus
            if confidence_score > 0.6:
                confidence_score += 0.15
            
            # Determine direction
            direction = 'BUY' if direction_votes['BUY'] > direction_votes['SELL'] else 'SELL'
            
            return {
                'should_trade': confidence_score > 0.65,
                'confidence': confidence_score,
                'direction': direction,
                'strength': min(3.0, max(0.5, confidence_score * 4)),
                'pattern_name': f"Multi-Pattern-{confidence_score:.2f}"
            }
            
        except Exception as e:
            return {'should_trade': False, 'confidence': 0.0}

    def calculate_dynamic_lot_size(self, signal: Signal) -> float:
        """Calculate advanced dynamic lot size with multiple factors"""
        try:
            # 1. Base lot จาก signal strength
            base_lot = self.base_lot * signal.strength
            
            # 2. Account equity adjustment
            account_info = mt5.account_info()
            if account_info:
                equity = account_info.equity
                balance = account_info.balance
                
                # Risk per trade = 1-3% ของ equity ตาม signal strength
                risk_percent = 0.01 + (signal.strength - 0.5) * 0.008  # 1%-3%
                risk_amount = equity * risk_percent
                
                # คำนวณ lot จาก risk amount (สมมติ stop loss 50 pips)
                pip_value = 1.0  # XAUUSD 1 pip = $1 per 0.01 lot
                stop_loss_pips = 50
                lot_from_risk = risk_amount / (stop_loss_pips * pip_value * 100)
                
                base_lot = min(base_lot, lot_from_risk)
            
            # 3. Portfolio balance adjustment (ปรับสมดุล BUY/SELL)
            total_volume = self.buy_volume + self.sell_volume
            if total_volume > 0:
                buy_ratio = self.buy_volume / total_volume
                sell_ratio = self.sell_volume / total_volume
                
                # เป้าหมาย 50:50 balance
                if signal.direction == 'BUY':
                    if buy_ratio > 0.65:  # BUY มากเกินไป
                        base_lot *= 0.5  # ลด lot
                    elif buy_ratio < 0.35:  # BUY น้อยเกินไป
                        base_lot *= 1.5  # เพิ่ม lot
                else:  # SELL
                    if sell_ratio > 0.65:  # SELL มากเกินไป
                        base_lot *= 0.5  # ลด lot
                    elif sell_ratio < 0.35:  # SELL น้อยเกินไป
                        base_lot *= 1.5  # เพิ่ม lot
            
            # 4. Market volatility adjustment
            if hasattr(self, 'recent_volatility'):
                if self.recent_volatility > 2.0:  # ตลาดผันผวนสูง
                    base_lot *= 0.7  # ลด lot
                elif self.recent_volatility < 0.5:  # ตลาดเงียบ
                    base_lot *= 1.3  # เพิ่ม lot
            
            # 5. Position count adjustment
            position_count = len(self.positions)
            if position_count > 30:
                base_lot *= 0.8  # มี position เยอะแล้ว ลด lot
            elif position_count < 10:
                base_lot *= 1.2  # มี position น้อย เพิ่ม lot
            
            # 6. Time-based adjustment (ตามเวลาเทรด)
            current_hour = datetime.now().hour
            if 22 <= current_hour or current_hour <= 2:  # เวลาเทรดหลัก
                base_lot *= 1.2
            elif 7 <= current_hour <= 9:  # เวลาเปิดตลาดเอเชีย
                base_lot *= 1.1
            elif 14 <= current_hour <= 16:  # เวลาเปิดตลาดอเมริกา
                base_lot *= 1.1
            else:  # เวลาเทรดเงียบ
                base_lot *= 0.8
            
            # 7. Portfolio health adjustment
            if self.portfolio_health < 50:
                base_lot *= 0.6  # Portfolio ไม่ดี ลด lot
            elif self.portfolio_health > 80:
                base_lot *= 1.3  # Portfolio ดี เพิ่ม lot
            
            # Round และ limit lot size
            lot_size = round(base_lot, 2)
            lot_size = max(0.01, min(2.0, lot_size))  # ขั้นต่ำ 0.01, สูงสุด 2.0
            
            return lot_size
            
        except Exception as e:
            self.log(f"Error calculating dynamic lot size: {str(e)}", "ERROR")
            return self.base_lot

    def calculate_lot_size(self, signal: Signal) -> float:
        """Calculate dynamic lot size - wrapper for new method"""
        return self.calculate_dynamic_lot_size(signal)

    def calculate_advanced_position_score(self, position: Position) -> dict:
        """คำนวณคะแนน position แบบขั้นสูง"""
        try:
            score_details = {
                'profit_score': 0,          # 0-25
                'age_score': 0,             # 0-15  
                'market_alignment': 0,      # 0-20
                'risk_reward_ratio': 0,     # 0-15
                'portfolio_contribution': 0, # 0-15
                'technical_position': 0,    # 0-10
                'total_score': 0
            }
            
            # 1. Profit Performance (25 points)
            profit_pct = self.calculate_profit_percent(position)
            if profit_pct >= 10:
                score_details['profit_score'] = 25
            elif profit_pct >= 5:
                score_details['profit_score'] = 20
            elif profit_pct >= 2:
                score_details['profit_score'] = 15
            elif profit_pct >= 0:
                score_details['profit_score'] = 10
            else:
                # Penalty for losses, but not too harsh
                score_details['profit_score'] = max(0, 10 + profit_pct)
            
            # 2. Age Factor (15 points)
            if position.ticket in self.position_tracker:
                age_hours = (datetime.now() - self.position_tracker[position.ticket]['birth_time']).total_seconds() / 3600
                if age_hours < 2:
                    score_details['age_score'] = 5  # Too young
                elif age_hours < 12:
                    score_details['age_score'] = 15  # Perfect age
                elif age_hours < 24:
                    score_details['age_score'] = 10  # Getting old
                else:
                    score_details['age_score'] = 5   # Too old
            
            # 3. Market Alignment (20 points)
            market_data = self.get_market_data()
            if market_data is not None:
                trend_strength = self.calculate_trend_strength(market_data)
                momentum = self.calculate_momentum_score(market_data)
                
                if position.type == "BUY":
                    if trend_strength > 0.6 and momentum > 0.6:
                        score_details['market_alignment'] = 20
                    elif trend_strength > 0.4 and momentum > 0.4:
                        score_details['market_alignment'] = 10
                else:  # SELL
                    if trend_strength < 0.4 and momentum < 0.4:
                        score_details['market_alignment'] = 20
                    elif trend_strength < 0.6 and momentum < 0.6:
                        score_details['market_alignment'] = 10
            
            # 4. Risk-Reward Ratio (15 points)
            if position.profit > 0:
                # Good profit deserves points
                score_details['risk_reward_ratio'] = min(15, (profit_pct / 5) * 15)
            else:
                # Manage risk for losing positions
                if profit_pct > -10:  # Acceptable loss
                    score_details['risk_reward_ratio'] = 10
                elif profit_pct > -20:  # High risk
                    score_details['risk_reward_ratio'] = 5
                else:  # Very high risk
                    score_details['risk_reward_ratio'] = 0
            
            # 5. Portfolio Contribution (15 points)
            if self.will_improve_balance_by_closing(position):
                score_details['portfolio_contribution'] = 15
            elif self.portfolio_health < 50 and position.profit > 0:
                score_details['portfolio_contribution'] = 10
            
            # 6. Technical Position (10 points)
            if hasattr(self, 'recent_volatility'):
                if self.recent_volatility < 1.0 and position.profit > 0:
                    score_details['technical_position'] = 10  # Good timing in low volatility
                elif self.recent_volatility > 2.0 and position.profit < 0:
                    score_details['technical_position'] = 0   # Bad timing in high volatility
                else:
                    score_details['technical_position'] = 5
            
            # Calculate total
            score_details['total_score'] = sum(v for k, v in score_details.items() if k != 'total_score')
            
            return score_details
            
        except Exception as e:
            self.log(f"Error calculating advanced score: {str(e)}", "ERROR")
            return {'total_score': 50}

    def will_improve_balance_by_closing(self, position: Position) -> bool:
        """ปรับปรุงการตรวจสอบ balance"""
        try:
            if len(self.positions) <= 1:
                return False
            
            total_volume = self.buy_volume + self.sell_volume
            if total_volume <= position.volume:
                return False
            
            current_buy_ratio = self.buy_volume / total_volume
            
            # คำนวณ balance หลังปิด
            if position.type == "BUY":
                new_buy_volume = self.buy_volume - position.volume
                new_sell_volume = self.sell_volume
            else:
                new_buy_volume = self.buy_volume
                new_sell_volume = self.sell_volume - position.volume
            
            new_total = new_buy_volume + new_sell_volume
            if new_total <= 0:
                return False
            
            new_buy_ratio = new_buy_volume / new_total
            
            # เช็คว่าใกล้ 50:50 มากขึ้นหรือไม่
            current_distance = abs(current_buy_ratio - 0.5)
            new_distance = abs(new_buy_ratio - 0.5)
            
            return new_distance < current_distance - 0.05  # ต้องดีขึ้นอย่างน้อย 5%
            
        except Exception as e:
            return False

    def can_trade(self) -> bool:
        """Check if trading is allowed based on various conditions"""
        try:
            # Check basic conditions
            if not self.mt5_connected or not self.trading_active:
                return False
            
            # Check position limit
            if len(self.positions) >= self.max_positions:
                self.log("Max positions reached", "WARNING")
                return False
            
            # Check daily trade limit
            if self.daily_trades >= self.max_daily_trades:
                self.log("Daily trade limit reached", "WARNING")
                return False
            
            # Check signal cooldown
            if (self.last_signal_time and 
                (datetime.now() - self.last_signal_time).seconds < self.signal_cooldown):
                return False
            
            # Check hourly signal limit
            now = datetime.now()
            hour_ago = now - timedelta(hours=1)
            recent_signals = [s for s in self.hourly_signals if s > hour_ago]
            if len(recent_signals) >= self.max_signals_per_hour:
                self.log("Hourly signal limit reached", "WARNING")
                return False
            
            # Check margin level
            account_info = mt5.account_info()
            if account_info and account_info.margin != 0:
                margin_level = (account_info.equity / account_info.margin) * 100
                if margin_level < self.min_margin_level:
                    self.log(f"Low margin level: {margin_level:.1f}%", "WARNING")
                    return False
            
            return True
            
        except Exception as e:
            self.log(f"Error checking trade conditions: {str(e)}", "ERROR")
            return False

    def execute_order(self, signal: Signal) -> bool:
        """Execute order with smart routing"""
        if not self.can_trade():
            return False
            
        try:
            # ใช้ Smart Signal Router
            router_result = self.smart_signal_router(signal)
            
            if router_result['action'] == 'skip':
                self.log(f"⏭️ Signal SKIPPED: {signal.direction} - {router_result['details']['reason']}")
                return False
            
            elif router_result['action'] == 'redirect':
                # ดำเนินการ redirect
                details = router_result['details']
                target_position = details['target_position']
                
                success = self.execute_redirect_close(target_position, signal, details['reason'])
                if success:
                    self.log(f"🎯 REDIRECT SUCCESS: ${details['profit_captured']:.2f} captured")
                    return True
                else:
                    # ถ้า redirect ล้มเหลว ให้ execute ปกติ
                    self.log("🔄 Redirect failed, executing normal order")
            
            # Execute ปกติ (หรือ fallback จาก redirect ที่ล้มเหลว)
            return self.execute_normal_order(signal)
            
        except Exception as e:
            self.log(f"Error in execute_order: {str(e)}", "ERROR")
            return False

    def execute_normal_order(self, signal: Signal) -> bool:
        """Execute normal market order"""
        try:
            lot_size = self.calculate_lot_size(signal)
            order_type = mt5.ORDER_TYPE_BUY if signal.direction == 'BUY' else mt5.ORDER_TYPE_SELL
            
            # Ensure we have a valid filling type
            if self.filling_type is None:
                self.filling_type = self.detect_broker_filling_type()
            
            request = {
                "action": mt5.TRADE_ACTION_DEAL,
                "symbol": self.symbol,
                "volume": lot_size,
                "type": order_type,
                "deviation": 20,
                "magic": 123456,
                "comment": f"AI_Smart_{signal.strength:.1f}",
                "type_time": mt5.ORDER_TIME_GTC,
                "type_filling": self.filling_type,
            }
            
            # Retry mechanism with different filling types if needed
            for attempt in range(3):
                result = mt5.order_send(request)
                
                if result.retcode == mt5.TRADE_RETCODE_DONE:
                    self.last_signal_time = datetime.now()
                    self.hourly_signals.append(datetime.now())
                    self.daily_trades += 1
                    self.total_signals += 1
                    
                    self.log(f"✅ Order executed: {signal.direction} {lot_size} lots")
                    self.log(f"   Reason: {signal.reason}")
                    return True
                    
                elif result.retcode == mt5.TRADE_RETCODE_INVALID_FILL:
                    # Try next filling type
                    current_index = self.filling_types_priority.index(self.filling_type)
                    if current_index < len(self.filling_types_priority) - 1:
                        self.filling_type = self.filling_types_priority[current_index + 1]
                        request["type_filling"] = self.filling_type
                        self.log(f"🔄 Retrying with different filling type: {self.filling_type}")
                    else:
                        self.log(f"❌ All filling types failed: {result.retcode}", "ERROR")
                        break
                else:
                    self.log(f"❌ Order failed (attempt {attempt + 1}): {result.retcode}", "WARNING")
                    time.sleep(1)
            
            self.log("❌ Order execution failed after 3 attempts", "ERROR")
            return False
            
        except Exception as e:
            self.log(f"Error executing normal order: {str(e)}", "ERROR")
            return False

    def update_positions(self):
        """Update position data and calculate metrics"""
        if not self.mt5_connected:
            return
            
        try:
            positions = mt5.positions_get(symbol=self.symbol)
            if positions is None:
                positions = []
            
            self.positions.clear()
            self.buy_volume = 0.0
            self.sell_volume = 0.0
            
            for pos in positions:
                current_price = mt5.symbol_info_tick(self.symbol).bid if pos.type == 1 else mt5.symbol_info_tick(self.symbol).ask
                profit_per_lot = pos.profit / pos.volume if pos.volume > 0 else 0
                
                # Classify efficiency
                if profit_per_lot > 100:
                    efficiency = "excellent"
                elif profit_per_lot > 50:
                    efficiency = "good"
                elif profit_per_lot > 0:
                    efficiency = "fair"
                else:
                    efficiency = "poor"
                
                # Assign role (simplified logic)
                role = self.assign_position_role(pos, profit_per_lot)
                
                position = Position(
                    ticket=pos.ticket,
                    symbol=pos.symbol,
                    type="BUY" if pos.type == 0 else "SELL",
                    volume=pos.volume,
                    open_price=pos.price_open,
                    current_price=current_price,
                    profit=pos.profit,
                    profit_per_lot=profit_per_lot,
                    role=role,
                    efficiency=efficiency
                )
                
                self.positions.append(position)
                
                # Update volume counters
                if pos.type == 0:  # BUY
                    self.buy_volume += pos.volume
                else:  # SELL
                    self.sell_volume += pos.volume
            
            # Calculate portfolio health
            self.calculate_portfolio_health()
            
        except Exception as e:
            self.log(f"Error updating positions: {str(e)}", "ERROR")

    def assign_position_role(self, position, profit_per_lot: float) -> str:
        """Assign role to position based on performance"""
        if profit_per_lot > 100:
            return OrderRole.MAIN.value
        elif profit_per_lot > 0:
            return OrderRole.SUPPORT.value
        elif profit_per_lot > -50:
            return OrderRole.HEDGE_GUARD.value
        else:
            return OrderRole.SACRIFICE.value

    def calculate_portfolio_health(self):
        """Calculate overall portfolio health score"""
        if not self.positions:
            self.portfolio_health = 100.0
            return
            
        try:
            total_profit = sum(pos.profit for pos in self.positions)
            total_volume = sum(pos.volume for pos in self.positions)
            
            # Volume balance factor
            total_vol = self.buy_volume + self.sell_volume
            balance_factor = 1.0
            if total_vol > 0:
                buy_ratio = self.buy_volume / total_vol
                imbalance = abs(buy_ratio - 0.5)
                balance_factor = 1.0 - (imbalance * 0.5)  # Max 25% penalty
            
            # Efficiency distribution
            excellent_count = len([p for p in self.positions if p.efficiency == "excellent"])
            good_count = len([p for p in self.positions if p.efficiency == "good"])
            poor_count = len([p for p in self.positions if p.efficiency == "poor"])
            
            efficiency_score = (excellent_count * 100 + good_count * 70 - poor_count * 30) / len(self.positions)
            efficiency_score = max(0, min(100, efficiency_score))
            
            # Position count factor
            position_factor = max(0.5, 1.0 - (len(self.positions) / self.max_positions) * 0.3)
            
            # Calculate final health score
            self.portfolio_health = efficiency_score * balance_factor * position_factor
            self.portfolio_health = max(0, min(100, self.portfolio_health))
            
        except Exception as e:
            self.log(f"Error calculating portfolio health: {str(e)}", "ERROR")
            self.portfolio_health = 50.0

    def get_smart_close_recommendations(self) -> List[str]:
        """Generate smart close recommendations"""
        recommendations = []
        
        try:
            if not self.positions:
                return recommendations
            
            # Find sacrifice candidates
            sacrifice_positions = [p for p in self.positions if p.role == OrderRole.SACRIFICE.value]
            if sacrifice_positions:
                total_sacrifice_loss = sum(p.profit for p in sacrifice_positions)
                main_positions = [p for p in self.positions if p.role == OrderRole.MAIN.value]
                total_main_profit = sum(p.profit for p in main_positions)
                
                if total_main_profit > abs(total_sacrifice_loss) * 1.2:
                    recommendations.append(f"Consider closing {len(sacrifice_positions)} sacrifice positions for net gain")
            
            # Volume imbalance recommendations
            total_vol = self.buy_volume + self.sell_volume
            if total_vol > 0:
                buy_ratio = self.buy_volume / total_vol
                if buy_ratio > 0.7:
                    recommendations.append("High BUY volume imbalance - consider closing some BUY positions")
                elif buy_ratio < 0.3:
                    recommendations.append("High SELL volume imbalance - consider closing some SELL positions")
            
            # Margin optimization
            account_info = mt5.account_info()
            if account_info and account_info.margin > 0:
                margin_level = (account_info.equity / account_info.margin) * 100
                if margin_level < 300:
                    poor_positions = [p for p in self.positions if p.efficiency == "poor"]
                    if poor_positions:
                        recommendations.append(f"Low margin warning - consider closing {len(poor_positions)} poor positions")
            
        except Exception as e:
            self.log(f"Error generating recommendations: {str(e)}", "ERROR")
        
        return recommendations

    def smart_signal_router(self, signal: Signal) -> dict:
        """
        Smart Signal Router - ตัดสินใจว่าจะ execute, redirect หรือ skip signal
        Returns: {'action': 'execute'/'redirect'/'skip', 'details': {...}}
        """
        try:
            result = {
                'action': 'execute',
                'details': {
                    'original_signal': signal,
                    'reason': 'Normal execution',
                    'redirect_target': None,
                    'profit_captured': 0.0
                }
            }
            
            if not self.smart_router_enabled or not self.positions:
                return result
            
            # 1. Check redirect cooldown
            if (self.last_redirect_time and 
                (datetime.now() - self.last_redirect_time).seconds < self.redirect_cooldown):
                return result
            
            # 2. Check redirect ratio limit
            if self.total_signals > 0:
                current_redirect_ratio = self.total_redirects / self.total_signals
                if current_redirect_ratio >= self.max_redirect_ratio:
                    result['details']['reason'] = 'Redirect ratio limit reached'
                    return result
            
            # 3. Analyze current balance
            total_volume = self.buy_volume + self.sell_volume
            if total_volume <= 0:
                return result
            
            buy_ratio = self.buy_volume / total_volume
            
            # 4. Check if redirect is beneficial
            redirect_analysis = self.analyze_redirect_opportunity(signal, buy_ratio)
            
            if redirect_analysis['should_redirect']:
                result['action'] = 'redirect'
                result['details'] = redirect_analysis
                self.log(f"🔄 Signal REDIRECTED: {signal.direction} → Close {redirect_analysis['target_type']}")
                self.log(f"   Reason: {redirect_analysis['reason']}")
                return result
            
            # 5. Check if should skip (extreme cases)
            if self.should_skip_signal(signal, buy_ratio):
                result['action'] = 'skip'
                result['details']['reason'] = 'Signal skipped for portfolio protection'
                return result
            
            return result
            
        except Exception as e:
            self.log(f"Error in smart signal router: {str(e)}", "ERROR")
            return {'action': 'execute', 'details': {'reason': 'Router error - default execute'}}

    def analyze_redirect_opportunity(self, signal: Signal, buy_ratio: float) -> dict:
        """วิเคราะห์โอกาสในการ redirect signal"""
        try:
            analysis = {
                'should_redirect': False,
                'target_type': None,
                'target_position': None,
                'reason': '',
                'profit_captured': 0.0,
                'balance_improvement': 0.0,
                'redirect_target': None
            }
            
            # Determine which type to close based on signal direction and balance
            if signal.direction == 'BUY' and buy_ratio > self.redirect_threshold:
                target_type = 'SELL'
                analysis['reason'] = f'BUY signal with high BUY ratio ({buy_ratio:.1%})'
            elif signal.direction == 'SELL' and (1 - buy_ratio) > self.redirect_threshold:
                target_type = 'BUY'
                analysis['reason'] = f'SELL signal with high SELL ratio ({1-buy_ratio:.1%})'
            else:
                return analysis
            
            # Find best candidate to close
            candidates = [p for p in self.positions if p.type == target_type]
            if not candidates:
                return analysis
            
            # Score each candidate
            best_candidate = None
            best_score = 0
            
            for pos in candidates:
                score = self.calculate_redirect_score(pos, signal)
                if score > best_score and score > 50:  # minimum score threshold
                    best_score = score
                    best_candidate = pos
            
            if best_candidate:
                # Calculate benefits
                volume_difference = abs(signal.strength * self.base_lot - best_candidate.volume)
                volume_match_score = max(0, 1 - (volume_difference / best_candidate.volume))
                
                # Calculate balance improvement
                new_buy_ratio = self.calculate_balance_after_close(best_candidate, buy_ratio)
                balance_improvement = abs(buy_ratio - 0.5) - abs(new_buy_ratio - 0.5)
                
                analysis.update({
                    'should_redirect': True,
                    'target_type': target_type,
                    'target_position': best_candidate,
                    'profit_captured': best_candidate.profit,
                    'balance_improvement': balance_improvement,
                    'redirect_target': best_candidate.ticket,
                    'volume_match_score': volume_match_score,
                    'redirect_score': best_score
                })
            
            return analysis
            
        except Exception as e:
            self.log(f"Error analyzing redirect opportunity: {str(e)}", "ERROR")
            return {'should_redirect': False}

    def calculate_redirect_score(self, position: Position, signal: Signal) -> float:
        """คำนวณคะแนนความเหมาะสมในการปิด position เพื่อ redirect (ใช้ %)"""
        try:
            score = 0.0
            profit_pct = self.calculate_profit_percent(position)
            
            # 1. Profit score (40 points) - ใช้ %
            if profit_pct >= self.min_profit_for_redirect_close_percent:
                profit_ratio = profit_pct / self.profit_harvest_threshold_percent
                score += min(40, profit_ratio * 30)
            else:
                return 0  # ไม่ปิดถ้ากำไรต่ำเกินไป
            
            # 2. Volume match score (20 points)
            signal_volume = self.calculate_lot_size(signal)
            volume_diff = abs(signal_volume - position.volume)
            volume_match = max(0, 1 - (volume_diff / max(signal_volume, position.volume)))
            score += volume_match * 20
            
            # 3. Age score (15 points)
            if position.ticket in self.position_tracker:
                age_hours = (datetime.now() - self.position_tracker[position.ticket]['birth_time']).total_seconds() / 3600
                if age_hours > 12:
                    score += min(15, age_hours / 2)
            
            # 4. Portfolio health bonus (15 points)
            if self.portfolio_health < 50 and profit_pct > 0:
                score += 15
            
            # 5. Efficiency score (10 points)
            if profit_pct > 10:
                score += 10
            elif profit_pct > 5:
                score += 7
            elif profit_pct > 2:
                score += 4
            
            return score
            
        except Exception as e:
            self.log(f"Error calculating redirect score: {str(e)}", "ERROR")
            return 0

    def calculate_adaptive_profit_target(self, position: Position) -> float:
        """คำนวณเป้าหมายกำไรแบบปรับตัว (เป็น %)"""
        try:
            base_target_pct = self.profit_harvest_threshold_percent
            
            # ปรับตาม portfolio health
            if self.portfolio_health < 40:
                base_target_pct *= 0.6
            elif self.portfolio_health > 80:
                base_target_pct *= 1.3
            
            # ปรับตาม balance
            if self.can_improve_balance_by_closing(position):
                base_target_pct *= 0.75
            
            # ปรับตาม volatility
            if hasattr(self, 'recent_volatility'):
                if self.recent_volatility > 2.0:
                    base_target_pct *= 0.8
                elif self.recent_volatility < 0.5:
                    base_target_pct *= 1.2
            
            return max(2.0, min(20.0, base_target_pct))
            
        except Exception as e:
            return self.profit_harvest_threshold_percent

    def calculate_balance_after_close(self, position: Position, current_buy_ratio: float) -> float:
        """คำนวณ balance หลังจากปิด position"""
        try:
            new_buy_volume = self.buy_volume - (position.volume if position.type == "BUY" else 0)
            new_sell_volume = self.sell_volume - (position.volume if position.type == "SELL" else 0)
            new_total = new_buy_volume + new_sell_volume
            
            if new_total <= 0:
                return 0.5
            
            return new_buy_volume / new_total
            
        except:
            return current_buy_ratio

    def should_skip_signal(self, signal: Signal, buy_ratio: float) -> bool:
        """ตรวจสอบว่าควร skip signal หรือไม่"""
        try:
            # Skip ถ้า balance เอียงมากและไม่มีตัวเลือกที่ดีให้ redirect
            if signal.direction == 'BUY' and buy_ratio > 0.8:
                sell_positions = [p for p in self.positions if p.type == "SELL"]
                profitable_sells = [p for p in sell_positions if p.profit_per_lot > self.min_profit_for_redirect_close]
                if not profitable_sells:
                    self.log(f"⏭️ Skipping BUY signal - extreme imbalance and no profitable SELLs")
                    return True
            
            elif signal.direction == 'SELL' and buy_ratio < 0.2:
                buy_positions = [p for p in self.positions if p.type == "BUY"]
                profitable_buys = [p for p in buy_positions if p.profit_per_lot > self.min_profit_for_redirect_close]
                if not profitable_buys:
                    self.log(f"⏭️ Skipping SELL signal - extreme imbalance and no profitable BUYs")
                    return True
            
            # Skip ถ้า position เยอะเกินไปและ margin ต่ำ
            if len(self.positions) > self.max_positions * 0.9:
                account_info = mt5.account_info()
                if account_info and account_info.margin > 0:
                    margin_level = (account_info.equity / account_info.margin) * 100
                    if margin_level < self.min_margin_level * 1.5:
                        self.log(f"⏭️ Skipping signal - high position count and low margin")
                        return True
            
            return False
            
        except Exception as e:
            self.log(f"Error checking skip conditions: {str(e)}", "ERROR")
            return False

    def execute_redirect_close(self, position: Position, original_signal: Signal, reason: str) -> bool:
        """ดำเนินการปิด position สำหรับ redirect"""
        try:
            close_type = mt5.ORDER_TYPE_SELL if position.type == "BUY" else mt5.ORDER_TYPE_BUY
            
            # Ensure we have a valid filling type
            if self.filling_type is None:
                self.filling_type = self.detect_broker_filling_type()
            
            request = {
                "action": mt5.TRADE_ACTION_DEAL,
                "symbol": self.symbol,
                "volume": position.volume,
                "type": close_type,
                "position": position.ticket,
                "deviation": 20,
                "magic": 123456,
                "comment": f"Smart_Redirect_{original_signal.direction[:1]}",
                "type_time": mt5.ORDER_TIME_GTC,
                "type_filling": self.filling_type,
            }
            
            result = mt5.order_send(request)
            
            if result.retcode == mt5.TRADE_RETCODE_DONE:
                # Update statistics
                self.total_redirects += 1
                self.successful_redirects += 1
                self.redirect_profit_captured += position.profit
                self.last_redirect_time = datetime.now()
                
                self.log(f"✅ Redirect successful: Closed {position.type} {position.volume} lots")
                self.log(f"   Profit captured: ${position.profit:.2f} (${position.profit_per_lot:.2f}/lot)")
                self.log(f"   Reason: {reason}")
                
                # Update position tracker
                if position.ticket in self.position_tracker:
                    del self.position_tracker[position.ticket]
                
                return True
                
            elif result.retcode == mt5.TRADE_RETCODE_INVALID_FILL:
                # Try with different filling type for close orders
                for filling_type in self.filling_types_priority:
                    if filling_type != self.filling_type:
                        request["type_filling"] = filling_type
                        result = mt5.order_send(request)
                        if result.retcode == mt5.TRADE_RETCODE_DONE:
                            self.log(f"✅ Redirect close successful with {filling_type}")
                            return True
                        
                self.log(f"❌ Redirect close failed with all filling types", "ERROR")
                return False
            else:
                self.log(f"❌ Redirect close failed: {result.retcode}", "WARNING")
                return False
                
        except Exception as e:
            self.log(f"Error executing redirect close: {str(e)}", "ERROR")
            return False

    def track_position_lifecycle(self, position: Position):
        """ติดตามวงจรชีวิตของแต่ละ position"""
        try:
            ticket = position.ticket
            
            if (ticket not in self.position_tracker) and (str(ticket) not in self.position_tracker):
                self.position_tracker[ticket] = {
                    'birth_time': datetime.now(),
                    'initial_price': position.open_price,
                    'max_profit': position.profit,
                    'min_profit': position.profit,
                    'role_history': [position.role],
                    'efficiency_history': [position.efficiency],
                    'peak_profit_per_lot': position.profit_per_lot,
                    'contribution_score': 0.0,
                    'hold_score': 50,
                    'adaptive_target': self.profit_harvest_threshold
                }
            
            tracker = self.position_tracker[ticket]
            
            # อัพเดทข้อมูล
            tracker['max_profit'] = max(tracker['max_profit'], position.profit)
            tracker['min_profit'] = min(tracker['min_profit'], position.profit)
            tracker['peak_profit_per_lot'] = max(tracker['peak_profit_per_lot'], position.profit_per_lot)
            
            # คำนวณ adaptive target
            tracker['adaptive_target'] = self.calculate_adaptive_profit_target(position)
            
            # คำนวณ hold score
            tracker['hold_score'] = self.calculate_hold_score(position, tracker)
            
            # อัพเดทประวัติ
            if tracker['role_history'][-1] != position.role:
                tracker['role_history'].append(position.role)
            if tracker['efficiency_history'][-1] != position.efficiency:
                tracker['efficiency_history'].append(position.efficiency)
                
        except Exception as e:
            self.log(f"Error tracking position {position.ticket}: {str(e)}", "ERROR")

    def calculate_adaptive_profit_target(self, position: Position) -> float:
        """คำนวณเป้าหมายกำไรแบบปรับตัว"""
        try:
            base_target = self.profit_harvest_threshold
            
            # ปรับตาม portfolio health
            if self.portfolio_health < 40:
                base_target *= 0.6
            elif self.portfolio_health > 80:
                base_target *= 1.3
            
            # ปรับตาม balance (ถ้าช่วย balance ได้ ลดเป้า)
            total_volume = self.buy_volume + self.sell_volume
            if total_volume > 0:
                buy_ratio = self.buy_volume / total_volume
                if abs(buy_ratio - 0.5) > self.balance_tolerance:
                    if self.can_improve_balance_by_closing(position):
                        base_target *= 0.75
            
            # ปรับตาม market volatility
            if hasattr(self, 'recent_volatility'):
                if self.recent_volatility > 2.0:
                    base_target *= 0.8
                elif self.recent_volatility < 0.5:
                    base_target *= 1.2
            
            # ปรับตามจำนวน positions
            if len(self.positions) > self.max_positions * 0.8:
                base_target *= 0.9
            
            return max(20.0, min(100.0, base_target))
            
        except Exception as e:
            return self.profit_harvest_threshold

    def calculate_hold_score(self, position: Position, tracker: dict) -> int:
        """คำนวณคะแนนการถือ position"""
        try:
            score = 50
            adaptive_target = tracker.get('adaptive_target', self.profit_harvest_threshold)
            
            # 1. Profit factor
            profit_ratio = position.profit_per_lot / adaptive_target
            if profit_ratio >= 1.2:
                score -= 35
            elif profit_ratio >= 1.0:
                score -= 25
            elif profit_ratio >= 0.5:
                score += 10
            elif profit_ratio > 0:
                score += 20
            else:
                score += 30
            
            # 2. Portfolio health factor
            if self.portfolio_health < self.emergency_mode_threshold:
                if position.profit > 0:
                    score -= 25
            elif self.portfolio_health > 80:
                score += 15
            
            # 3. Balance factor
            if self.can_improve_balance_by_closing(position):
                score -= 10
            
            # 4. Age factor
            age_hours = (datetime.now() - tracker['birth_time']).total_seconds() / 3600
            if age_hours > self.max_hold_hours:
                score -= 20
            elif age_hours > 24:
                score -= 10
            
            return max(0, min(100, score))
            
        except Exception as e:
            return 50

    def can_improve_balance_by_closing(self, position: Position) -> bool:
        """ตรวจสอบว่าการปิดจะช่วย balance ได้หรือไม่"""
        try:
            if len(self.positions) <= 1:
                return False
            
            total_volume = self.buy_volume + self.sell_volume
            if total_volume <= position.volume:
                return False
            
            current_buy_ratio = self.buy_volume / total_volume
            new_buy_ratio = self.calculate_balance_after_close(position, current_buy_ratio)
            
            current_distance = abs(current_buy_ratio - 0.5)
            new_distance = abs(new_buy_ratio - 0.5)
            
            return new_distance < current_distance
            
        except:
            return False

    def smart_position_management(self):
        """ระบบจัดการ position อัจฉริยะ (เพิ่ม hedge management)"""
        if not self.mt5_connected or not self.positions:
            return
        
        try:
            # ติดตามทุก position
            for position in self.positions:
                self.track_position_lifecycle(position)
            
            # 1. ระบบจัดการ drawdown & hedge ก่อน
            self.drawdown_management_system()
            
            # 2. ลองปิดแบบคู่/กลุ่ม (ประหยัด margin มากกว่า)
            self.smart_pair_group_management()
            
            # 3. ปิดแบบปกติ (ถ้าไม่มีโอกาสคู่/กลุ่มดี)
            self.execute_flexible_closes()
            
            # 4. ทำความสะอาด tracker
            self.cleanup_closed_positions()
            
        except Exception as e:
            self.log(f"Error in smart position management: {str(e)}", "ERROR")

    def execute_flexible_closes(self):
        """ปิด position แบบยืดหยุ่น"""
        try:
            closes_this_cycle = 0
            max_closes = 2 if self.gentle_management else 3
            
            for position in self.positions:
                if closes_this_cycle >= max_closes:
                    break
                
                tracker = self.position_tracker.get(position.ticket, {})
                hold_score = tracker.get('hold_score', 50)
                adaptive_target = tracker.get('adaptive_target', self.profit_harvest_threshold)
                
                should_close = False
                reason = ""
                
                # เงื่อนไขการปิดแบบยืดหยุ่น
                if position.profit_per_lot >= adaptive_target * 1.3 and hold_score <= 15:
                    should_close = True
                    reason = f"Exceed target 130%: {position.profit_per_lot:.1f}$"
                
                elif (position.profit_per_lot >= adaptive_target and 
                      hold_score <= 25 and 
                      self.portfolio_health < 60):
                    should_close = True
                    reason = f"Target reached + Portfolio concern"
                
                elif (self.portfolio_health < self.emergency_mode_threshold and 
                      position.profit_per_lot > 30 and 
                      hold_score <= 30):
                    should_close = True
                    reason = "Emergency profit-taking"
                
                elif (len(self.positions) > self.max_positions * 0.9 and
                      position.profit_per_lot > 40 and
                      hold_score <= 20):
                    should_close = True
                    reason = "Position count optimization"
                
                if should_close:
                    success = self.close_position_smart(position, reason)
                    if success:
                        closes_this_cycle += 1
                        time.sleep(1)  # Small delay between closes
                
        except Exception as e:
            self.log(f"Error executing flexible closes: {str(e)}", "ERROR")

    def close_position_smart(self, position: Position, reason: str) -> bool:
        """ปิด position อย่างชาญฉลาด"""
        try:
            close_type = mt5.ORDER_TYPE_SELL if position.type == "BUY" else mt5.ORDER_TYPE_BUY
            
            # Ensure we have a valid filling type
            if self.filling_type is None:
                self.filling_type = self.detect_broker_filling_type()
            
            request = {
                "action": mt5.TRADE_ACTION_DEAL,
                "symbol": self.symbol,
                "volume": position.volume,
                "type": close_type,
                "position": position.ticket,
                "deviation": 20,
                "magic": 123456,
                "comment": f"Smart_{reason[:12]}",
                "type_time": mt5.ORDER_TIME_GTC,
                "type_filling": self.filling_type,
            }
            
            result = mt5.order_send(request)
            
            if result.retcode == mt5.TRADE_RETCODE_DONE:
                self.log(f"✅ Smart close: {position.ticket} - {reason}")
                self.log(f"   Profit: ${position.profit:.2f} (${position.profit_per_lot:.2f}/lot)")
                return True
            elif result.retcode == mt5.TRADE_RETCODE_INVALID_FILL:
                # Try with different filling types
                for filling_type in self.filling_types_priority:
                    if filling_type != self.filling_type:
                        request["type_filling"] = filling_type
                        result = mt5.order_send(request)
                        if result.retcode == mt5.TRADE_RETCODE_DONE:
                            self.log(f"✅ Smart close successful with {filling_type}")
                            return True
                            
                self.log(f"❌ Smart close failed with all filling types", "ERROR")
                return False
            else:
                self.log(f"❌ Smart close failed: {result.retcode}", "WARNING")
                return False
                
        except Exception as e:
            self.log(f"Error in smart close: {str(e)}", "ERROR")
            return False

    def cleanup_closed_positions(self):
        """ทำความสะอาด tracker"""
        try:
            active_tickets = {pos.ticket for pos in self.positions}
            closed_tickets = [ticket for ticket in self.position_tracker.keys() 
                            if ticket not in active_tickets]
            
            for ticket in closed_tickets:
                del self.position_tracker[ticket]
                
        except Exception as e:
            self.log(f"Error cleaning up: {str(e)}", "ERROR")

    def get_smart_management_stats(self) -> dict:
        """สถิติการจัดการแบบชาญฉลาด"""
        try:
            stats = {
                'total_redirects': self.total_redirects,
                'successful_redirects': self.successful_redirects,
                'redirect_success_rate': (self.successful_redirects / max(1, self.total_redirects)) * 100,
                'redirect_profit_captured': self.redirect_profit_captured,
                'avg_profit_per_redirect': self.redirect_profit_captured / max(1, self.successful_redirects),
                'redirect_ratio': (self.total_redirects / max(1, self.total_signals)) * 100,
                'active_trackers': len(self.position_tracker),
                'positions_ready_to_close': 0,
                'avg_hold_score': 0
            }
            
            if self.positions:
                total_hold_score = 0
                ready_count = 0
                
                for position in self.positions:
                    tracker = self.position_tracker.get(position.ticket, {})
                    hold_score = tracker.get('hold_score', 50)
                    total_hold_score += hold_score
                    
                    if hold_score <= 25:
                        ready_count += 1
                
                stats['avg_hold_score'] = total_hold_score / len(self.positions)
                stats['positions_ready_to_close'] = ready_count
            
            return stats
            
        except Exception as e:
            self.log(f"Error getting smart stats: {str(e)}", "ERROR")
            return {}

    def trading_loop(self):
        """Main trading loop with auto-save"""
        self.log("🧠 Smart Trading System Started with State Management")
        last_save_time = datetime.now()
        
        while self.trading_active:
            try:
                if not self.mt5_connected:
                    self.log("⚠️ MT5 not connected, waiting...", "WARNING")
                    time.sleep(5)
                    continue
                
                # Update positions
                self.update_positions()
                self.log(f"📊 Updated positions: {len(self.positions)} active")
                
                # Smart Position Management (ทุก 30 วินาที)
                if (not self.last_efficiency_check or 
                    (datetime.now() - self.last_efficiency_check).seconds >= self.position_efficiency_check_interval):
                    self.smart_position_management()
                    self.last_efficiency_check = datetime.now()
                    self.log("🧠 Smart position management executed")
                
                # Market analysis and signal processing
                self.log("📈 Getting market data...")
                market_data = self.get_market_data()
                
                if (market_data is not None):
                    self.log(f"✅ Market data received: {len(market_data)} candles")
                    signal = self.analyze_mini_trend(market_data)
                    
                    if signal:
                        self.log(f"🚨 SIGNAL FOUND: {signal.direction} strength {signal.strength:.1f}")
                        self.log(f"   Reason: {signal.reason}")
                        
                        if self.can_trade():
                            self.log(f"✅ Trade conditions OK, executing order...")
                            success = self.execute_order(signal)  # ใช้ smart router
                            if success:
                                self.successful_signals += 1
                                self.log(f"🎯 Order execution successful!")
                            else:
                                self.log(f"❌ Order execution failed")
                        else:
                            self.log(f"⏸️ Cannot trade - checking conditions...")
                            # Debug why can't trade
                            self.debug_trade_conditions()
                    else:
                        self.log("📊 No signal detected in current market data")
                        # Debug market conditions
                        self.debug_market_conditions(market_data)
                else:
                    self.log("❌ No market data received", "WARNING")
                
                # Cleanup old signals
                hour_ago = datetime.now() - timedelta(hours=1)
                old_count = len(self.hourly_signals)
                self.hourly_signals = [s for s in self.hourly_signals if s > hour_ago]
                if old_count != len(self.hourly_signals):
                    self.log(f"🧹 Cleaned up {old_count - len(self.hourly_signals)} old signals")
                
                # Auto-save ทุก 5 นาที
                if (datetime.now() - last_save_time).seconds >= 300:  # 5 minutes
                    self.auto_save_state()
                    last_save_time = datetime.now()
                
                time.sleep(5)  # 5-second cycle
                
            except Exception as e:
                self.log(f"Error in trading loop: {str(e)}", "ERROR")
                # Emergency recovery
                self.emergency_state_recovery()
                time.sleep(10)
        
        # Save state เมื่อหยุด trading
        self.save_trading_state()
        self.log("🛑 Smart Trading System Stopped - State Saved")

    def debug_trade_conditions(self):
        """Debug why trading is not allowed"""
        try:
            conditions = []
            
            if not self.mt5_connected:
                conditions.append("❌ MT5 not connected")
            else:
                conditions.append("✅ MT5 connected")
                
            if not self.trading_active:
                conditions.append("❌ Trading not active")
            else:
                conditions.append("✅ Trading active")
                
            if len(self.positions) >= self.max_positions:
                conditions.append(f"❌ Max positions reached: {len(self.positions)}/{self.max_positions}")
            else:
                conditions.append(f"✅ Position count OK: {len(self.positions)}/{self.max_positions}")
                
            if self.daily_trades >= self.max_daily_trades:
                conditions.append(f"❌ Daily trade limit: {self.daily_trades}/{self.max_daily_trades}")
            else:
                conditions.append(f"✅ Daily trades OK: {self.daily_trades}/{self.max_daily_trades}")
                
            # Signal cooldown
            if self.last_signal_time:
                seconds_since = (datetime.now() - self.last_signal_time).seconds
                if seconds_since < self.signal_cooldown:
                    conditions.append(f"❌ Signal cooldown: {seconds_since}/{self.signal_cooldown}s")
                else:
                    conditions.append(f"✅ Signal cooldown OK: {seconds_since}s ago")
            else:
                conditions.append("✅ No previous signals")
                
            # Hourly limit
            recent_count = len(self.hourly_signals)
            if recent_count >= self.max_signals_per_hour:
                conditions.append(f"❌ Hourly limit: {recent_count}/{self.max_signals_per_hour}")
            else:
                conditions.append(f"✅ Hourly signals OK: {recent_count}/{self.max_signals_per_hour}")
                
            # Margin check
            account_info = mt5.account_info()
            if account_info and account_info.margin > 0:
                margin_level = (account_info.equity / account_info.margin) * 100
                if margin_level < self.min_margin_level:
                    conditions.append(f"❌ Low margin: {margin_level:.1f}%")
                else:
                    conditions.append(f"✅ Margin OK: {margin_level:.1f}%")
            else:
                conditions.append("✅ No margin used")
                
            self.log("🔍 TRADE CONDITIONS DEBUG:")
            for condition in conditions:
                self.log(f"   {condition}")
                
        except Exception as e:
            self.log(f"Error debugging trade conditions: {str(e)}", "ERROR")

    def debug_market_conditions(self, df):
        """Debug market analysis conditions"""
        try:
            if df is None or len(df) < 3:
                self.log("🔍 MARKET DEBUG: Insufficient data")
                return
                
            last_3 = df.tail(3)
            current_candle = last_3.iloc[-1]
            
            # Count conditions
            green_count = last_3['is_green'].sum()
            red_count = 3 - green_count
            avg_body_ratio = last_3['body_ratio'].mean()
            avg_movement = last_3['movement'].mean()
            current_is_green = current_candle['is_green']
            
            self.log("🔍 MARKET CONDITIONS DEBUG:")
            self.log(f"   Green candles: {green_count}/3")
            self.log(f"   Red candles: {red_count}/3")
            self.log(f"   Avg body ratio: {avg_body_ratio:.2f}% (need ≥5%)")
            self.log(f"   Avg movement: {avg_movement:.4f} points (need ≥0.2)")
            self.log(f"   Current candle: {'Green' if current_is_green else 'Red'}")
            
            # Check BUY conditions
            buy_possible = (green_count >= 2 and 
                           avg_body_ratio >= 5.0 and 
                           avg_movement >= 0.2 and
                           current_is_green)
            
            # Check SELL conditions  
            sell_possible = (red_count >= 2 and 
                            avg_body_ratio >= 5.0 and 
                            avg_movement >= 0.2 and
                            not current_is_green)
            
            if buy_possible:
                self.log("   ✅ BUY signal conditions MET")
            elif sell_possible:
                self.log("   ✅ SELL signal conditions MET")
            else:
                self.log("   ❌ No signal conditions met")
                
            # Detailed breakdown
            if green_count >= 2 and current_is_green:
                self.log("   ✅ BUY trend OK")
            elif red_count >= 2 and not current_is_green:
                self.log("   ✅ SELL trend OK")
            else:
                self.log("   ❌ Trend conditions not met")
                
            if avg_body_ratio < 5.0:
                self.log(f"   ❌ Body ratio too small: {avg_body_ratio:.2f}%")
            else:
                self.log(f"   ✅ Body ratio OK: {avg_body_ratio:.2f}%")
                
            if avg_movement < 0.2:
                self.log(f"   ❌ Movement too small: {avg_movement:.4f}")
            else:
                self.log(f"   ✅ Movement OK: {avg_movement:.4f}")
                
        except Exception as e:
            self.log(f"Error debugging market conditions: {str(e)}", "ERROR")

    def calculate_profit_percent(self, position: Position) -> float:
        """คำนวณกำไรเป็น % ต่อ lot"""
        try:
            if position.volume <= 0:
                return 0.0
            
            # คำนวณ profit per lot as percentage
            # สมมติ 1 lot XAUUSD = $1000 margin requirement
            margin_per_lot = 1000.0  # ปรับตามโบรกเกอร์
            profit_percent = (position.profit_per_lot / margin_per_lot) * 100
            
            return profit_percent
            
        except Exception as e:
            self.log(f"Error calculating profit percent: {str(e)}", "ERROR")
            return 0.0

    def find_profitable_pairs(self) -> List[dict]:
        """หาคู่ไม้ที่กำไร + ขาดทุน = กำไรรวม (เป็น %)"""
        pairs = []
        
        try:
            if not self.pair_closing_enabled or len(self.positions) < 2:
                return pairs
            
            # แยกไม้กำไรและขาดทุน
            profitable_positions = [p for p in self.positions if self.calculate_profit_percent(p) > 0]
            loss_positions = [p for p in self.positions 
                            if self.calculate_profit_percent(p) < 0 
                            and self.calculate_profit_percent(p) >= self.max_loss_percent]
            
            if not profitable_positions or not loss_positions:
                return pairs
            
            # หาคู่ที่ดีที่สุด
            for profit_pos in profitable_positions:
                for loss_pos in loss_positions:
                    profit_pct = self.calculate_profit_percent(profit_pos)
                    loss_pct = self.calculate_profit_percent(loss_pos)
                    net_profit_pct = profit_pct + loss_pct  # loss_pct เป็นลบอยู่แล้ว
                    
                    if net_profit_pct >= self.min_pair_profit_percent:
                        pair_score = self.calculate_pair_score_percent(profit_pos, loss_pos, net_profit_pct)
                        
                        pairs.append({
                            'type': 'pair',
                            'positions': [profit_pos, loss_pos],
                            'net_profit': profit_pos.profit + loss_pos.profit,
                            'net_profit_percent': net_profit_pct,
                            'score': pair_score,
                            'profit_position': profit_pos,
                            'loss_position': loss_pos,
                            'reason': f'Pair close: {profit_pct:.1f}% + {loss_pct:.1f}% = {net_profit_pct:.1f}%'
                        })
            
            # เรียงตามคะแนน
            pairs.sort(key=lambda x: x['score'], reverse=True)
            return pairs[:5]  # ส่งคืนแค่ 5 คู่ที่ดีที่สุด
            
        except Exception as e:
            self.log(f"Error finding profitable pairs: {str(e)}", "ERROR")
            return []

    def calculate_pair_score_percent(self, profit_pos: Position, loss_pos: Position, net_profit_pct: float) -> float:
        """คำนวณคะแนนคู่ไม้ (ใช้ %)"""
        try:
            score = 0.0
            
            # 1. Net profit percentage score (40 points)
            profit_ratio = net_profit_pct / self.min_pair_profit_percent
            score += min(40, profit_ratio * 20)
            
            # 2. Volume balance score (20 points)
            volume_diff = abs(profit_pos.volume - loss_pos.volume)
            avg_volume = (profit_pos.volume + loss_pos.volume) / 2
            volume_balance = max(0, 1 - (volume_diff / avg_volume)) if avg_volume > 0 else 0
            score += volume_balance * 20
            
            # 3. Age factor (15 points)
            if (profit_pos.ticket in self.position_tracker and 
                loss_pos.ticket in self.position_tracker):
                profit_age = (datetime.now() - self.position_tracker[profit_pos.ticket]['birth_time']).total_seconds() / 3600
                loss_age = (datetime.now() - self.position_tracker[loss_pos.ticket]['birth_time']).total_seconds() / 3600
                avg_age = (profit_age + loss_age) / 2
                if avg_age > 6:  # หลัง 6 ชั่วโมง
                    score += min(15, avg_age / 2)
            
            # 4. Portfolio health bonus (15 points)
            if self.portfolio_health < 50:
                score += 15
            elif self.portfolio_health < 30:
                score += 25  # Emergency bonus
            
            # 5. Balance improvement (10 points)
            if self.will_improve_balance_by_closing_pair(profit_pos, loss_pos):
                score += 10
            
            return score
            
        except Exception as e:
            self.log(f"Error calculating pair score: {str(e)}", "ERROR")
            return 0

    def find_profitable_groups(self) -> List[dict]:
        """หากลุ่มไม้ที่รวมกันได้กำไร (ใช้ %)"""
        groups = []
        
        try:
            if not self.group_closing_enabled or len(self.positions) < 3:
                return groups
            
            # แยกตามประเภท
            buy_positions = [p for p in self.positions if p.type == "BUY"]
            sell_positions = [p for p in self.positions if p.type == "SELL"]
            
            # หากลุ่ม BUY ที่ได้กำไรรวม
            if len(buy_positions) >= 2:
                buy_group = self.analyze_group_profitability(buy_positions, "BUY")
                if buy_group:
                    groups.append(buy_group)
            
            # หากลุ่ม SELL ที่ได้กำไรรวม
            if len(sell_positions) >= 2:
                sell_group = self.analyze_group_profitability(sell_positions, "SELL")
                if sell_group:
                    groups.append(sell_group)
            
            # หากลุ่มผสม (BUY + SELL)
            mixed_group = self.analyze_mixed_group_profitability(buy_positions, sell_positions)
            if mixed_group:
                groups.append(mixed_group)
            
            # เรียงตามคะแนน
            groups.sort(key=lambda x: x['score'], reverse=True)
            return groups[:3]  # ส่งคืนแค่ 3 กลุ่มที่ดีที่สุด
            
        except Exception as e:
            self.log(f"Error finding profitable groups: {str(e)}", "ERROR")
            return []

    def analyze_group_profitability(self, positions: List[Position], group_type: str) -> Optional[dict]:
        """วิเคราะห์กำไรของกลุ่ม positions"""
        try:
            if len(positions) < 2:
                return None
            
            # คำนวณกำไรรวมเป็น %
            total_profit = sum(p.profit for p in positions)
            total_volume = sum(p.volume for p in positions)
            avg_profit_percent = sum(self.calculate_profit_percent(p) for p in positions) / len(positions)
            
            if avg_profit_percent >= self.min_group_profit_percent:
                score = self.calculate_group_score(positions, avg_profit_percent, group_type)
                
                return {
                    'type': 'group',
                    'group_type': group_type,
                    'positions': positions,
                    'net_profit': total_profit,
                    'avg_profit_percent': avg_profit_percent,
                    'score': score,
                    'total_volume': total_volume,
                    'reason': f'{group_type} group close: {avg_profit_percent:.1f}% avg profit ({len(positions)} positions)'
                }
            
            return None
            
        except Exception as e:
            self.log(f"Error analyzing group profitability: {str(e)}", "ERROR")
            return None

    def analyze_mixed_group_profitability(self, buy_positions: List[Position], sell_positions: List[Position]) -> Optional[dict]:
        """วิเคราะห์กลุ่มผสม BUY+SELL"""
        try:
            if len(buy_positions) < 1 or len(sell_positions) < 1:
                return None
            
            # หาชุดคู่ที่ดีที่สุด
            best_combination = None
            best_score = 0
            
            # ลองรวม 1-2 BUY + 1-2 SELL
            for buy_count in range(1, min(3, len(buy_positions) + 1)):
                for sell_count in range(1, min(3, len(sell_positions) + 1)):
                    if buy_count + sell_count < 3:  # ต้องมีอย่างน้อย 3 ตัว
                        continue
                    
                    # เลือก positions ที่ดีที่สุด
                    selected_buys = sorted(buy_positions, key=lambda p: self.calculate_profit_percent(p), reverse=True)[:buy_count]
                    selected_sells = sorted(sell_positions, key=lambda p: self.calculate_profit_percent(p), reverse=True)[:sell_count]
                    
                    combined_positions = selected_buys + selected_sells
                    total_profit = sum(p.profit for p in combined_positions)
                    avg_profit_pct = sum(self.calculate_profit_percent(p) for p in combined_positions) / len(combined_positions)
                    
                    if avg_profit_pct >= self.min_group_profit_percent:
                        score = self.calculate_group_score(combined_positions, avg_profit_pct, "MIXED")
                        
                        if score > best_score:
                            best_score = score
                            best_combination = {
                                'type': 'mixed_group',
                                'group_type': 'MIXED',
                                'positions': combined_positions,
                                'net_profit': total_profit,
                                'avg_profit_percent': avg_profit_pct,
                                'score': score,
                                'buy_count': buy_count,
                                'sell_count': sell_count,
                                'reason': f'Mixed group: {buy_count}BUY+{sell_count}SELL, {avg_profit_pct:.1f}% avg'
                            }
            
            return best_combination
            
        except Exception as e:
            self.log(f"Error analyzing mixed group: {str(e)}", "ERROR")
            return None

    def calculate_group_score(self, positions: List[Position], avg_profit_pct: float, group_type: str) -> float:
        """คำนวณคะแนนกลุ่ม"""
        try:
            score = 0.0
            
            # 1. Average profit percentage score (35 points)
            profit_ratio = avg_profit_pct / self.min_group_profit_percent
            score += min(35, profit_ratio * 25)
            
            # 2. Group size bonus (20 points)
            group_size = len(positions)
            if group_size >= 5:
                score += 20
            elif group_size >= 3:
                score += 15
            else:
                score += 10
            
            # 3. Balance factor (20 points)
            if group_type == "MIXED":
                score += 20  # Mixed groups help balance
            elif self.portfolio_needs_rebalancing():
                buy_volume = sum(p.volume for p in positions if p.type == "BUY")
                sell_volume = sum(p.volume for p in positions if p.type == "SELL")
                
                if self.buy_volume > self.sell_volume and sell_volume > buy_volume:
                    score += 15  # ปิด SELL เมื่อ BUY มากกว่า
                elif self.sell_volume > self.buy_volume and buy_volume > sell_volume:
                    score += 15  # ปิด BUY เมื่อ SELL มากกว่า
            
            # 4. Portfolio health bonus (15 points)
            if self.portfolio_health < 40:
                score += 15
            
            # 5. Age factor (10 points)
            avg_age = 0
            for pos in positions:
                if pos.ticket in self.position_tracker:
                    age_hours = (datetime.now() - self.position_tracker[pos.ticket]['birth_time']).total_seconds() / 3600
                    avg_age += age_hours
            
            if len(positions) > 0:
                avg_age /= len(positions)
                if avg_age > 12:
                    score += min(10, avg_age / 2)
            
            return score
            
        except Exception as e:
            self.log(f"Error calculating group score: {str(e)}", "ERROR")
            return 0

    def will_improve_balance_by_closing_pair(self, pos1: Position, pos2: Position) -> bool:
        """ตรวจสอบว่าการปิดคู่จะช่วย balance ได้หรือไม่"""
        try:
            if len(self.positions) <= 2:
                return False
            
            total_volume = self.buy_volume + self.sell_volume
            if total_volume <= 0:
                return False
            
            current_buy_ratio = self.buy_volume / total_volume
            
            # คำนวณ balance หลังปิด
            new_buy_volume = self.buy_volume - (pos1.volume if pos1.type == "BUY" else 0) - (pos2.volume if pos1.type == "BUY" else 0)
            new_sell_volume = self.sell_volume - (pos1.volume if pos1.type == "SELL" else 0) - (pos2.volume if pos1.type == "SELL" else 0)
            new_total = new_buy_volume + new_sell_volume
            
            if new_total <= 0:
                return False
            
            new_buy_ratio = new_buy_volume / new_total
            
            # เช็คว่าใกล้ 50:50 มากขึ้นหรือไม่
            current_distance = abs(current_buy_ratio - 0.5)
            new_distance = abs(new_buy_ratio - 0.5)
            
            return new_distance < current_distance
            
        except:
            return False

    def portfolio_needs_rebalancing(self) -> bool:
        """ตรวจสอบว่า portfolio ต้องการ rebalance หรือไม่"""
        try:
            total_volume = self.buy_volume + self.sell_volume
            if total_volume <= 0:
                return False
            
            buy_ratio = self.buy_volume / total_volume
            return abs(buy_ratio - 0.5) > self.balance_tolerance
            
        except:
            return False

    def execute_pair_close(self, pair_data: dict) -> bool:
        """ปิดคู่ positions"""
        try:
            positions = pair_data['positions']
            
            success_count = 0
            for position in positions:
                if self.close_position_smart(position, f"Pair close: {pair_data['net_profit_percent']:.1f}%"):
                    success_count += 1
                    time.sleep(0.5)  # หน่วงเล็กน้อย
            
            if success_count == len(positions):
                self.total_pair_closes += 1
                self.successful_pair_closes += 1
                self.pair_profit_captured += pair_data['net_profit']
                
                self.log(f"✅ Pair close SUCCESS: {pair_data['reason']}")
                self.log(f"   Net profit: ${pair_data['net_profit']:.2f} ({pair_data['net_profit_percent']:.1f}%)")
                return True
            else:
                self.log(f"❌ Pair close PARTIAL: {success_count}/{len(positions)} positions closed")
                return False
                
        except Exception as e:
            self.log(f"Error executing pair close: {str(e)}", "ERROR")
            return False

    def execute_group_close(self, group_data: dict) -> bool:
        """ปิดกลุ่ม positions"""
        try:
            positions = group_data['positions']
            
            success_count = 0
            for position in positions:
                if self.close_position_smart(position, f"Group close: {group_data['avg_profit_percent']:.1f}%"):
                    success_count += 1
                    time.sleep(0.5)  # หน่วงเล็กน้อย
            
            if success_count >= len(positions) * 0.8:  # 80% สำเร็จถือว่าโอเค
                self.total_group_closes += 1
                self.group_profit_captured += group_data['net_profit']
                
                self.log(f"✅ Group close SUCCESS: {group_data['reason']}")
                self.log(f"   Net profit: ${group_data['net_profit']:.2f} ({group_data['avg_profit_percent']:.1f}%)")
                self.log(f"   Positions closed: {success_count}/{len(positions)}")
                return True
            else:
                self.log(f"❌ Group close FAILED: {success_count}/{len(positions)} positions closed")
                return False
                
        except Exception as e:
            self.log(f"Error executing group close: {str(e)}", "ERROR")
            return False

    def smart_pair_group_management(self):
        """ระบบจัดการแบบคู่และกลุ่ม"""
        if not self.mt5_connected or len(self.positions) < 2:
            return
        
        try:
            # 1. หาโอกาสปิดคู่
            profitable_pairs = self.find_profitable_pairs()
            if profitable_pairs:
                best_pair = profitable_pairs[0]
                if best_pair['score'] > 70:  # คะแนนสูงพอ
                    self.execute_pair_close(best_pair)
                    return  # ปิดคู่แล้วพอ cycle นี้
            
            # 2. หาโอกาสปิดกลุ่ม (ถ้าไม่มีคู่ดี)
            profitable_groups = self.find_profitable_groups()
            if profitable_groups:
                best_group = profitable_groups[0]
                if best_group['score'] > 80:  # คะแนนสูงกว่าเพราะปิดหลายตัว
                    self.execute_group_close(best_group)
            
        except Exception as e:
            self.log(f"Error in smart pair/group management: {str(e)}", "ERROR")

    def get_pair_group_stats(self) -> dict:
        """สถิติการปิดแบบคู่และกลุ่ม"""
        try:
            stats = {
                'total_pair_closes': self.total_pair_closes,
                'successful_pair_closes': self.successful_pair_closes,
                'pair_success_rate': (self.successful_pair_closes / max(1, self.total_pair_closes)) * 100,
                'pair_profit_captured': self.pair_profit_captured,
                'total_group_closes': self.total_group_closes,
                'group_profit_captured': self.group_profit_captured,
                'total_smart_profit': self.pair_profit_captured + self.group_profit_captured,
                'available_pairs': 0,
                'available_groups': 0
            }
            
            # นับโอกาสปัจจุบัน
            pairs = self.find_profitable_pairs()
            groups = self.find_profitable_groups()
            
            stats['available_pairs'] = len([p for p in pairs if p['score'] > 50])
            stats['available_groups'] = len([g for g in groups if g['score'] > 60])
            
            return stats
            
        except Exception as e:
            self.log(f"Error getting pair/group stats: {str(e)}", "ERROR")
            return {}

    def analyze_position_drawdown(self, position: Position) -> dict:
        """วิเคราะห์ระดับ drawdown ของ position"""
        try:
            analysis = {
                'position': position,
                'current_drawdown_pips': 0,
                'drawdown_level': 'SAFE',
                'recommended_action': 'HOLD',
                'distance_from_entry': 0,
                'risk_score': 0,
                'needs_hedge': False,
                'hedge_suggestions': []
            }
            
            # ดึงราคาปัจจุบัน
            current_tick = mt5.symbol_info_tick(self.symbol)
            if not current_tick:
                return analysis
            
            current_price = current_tick.ask if position.type == "BUY" else current_tick.bid
            
            # คำนวณระยะห่างเป็น pips
            if position.type == "BUY":
                distance_pips = (position.open_price - current_price) * 100  # ติดลบถ้าราคาตก
            else:  # SELL
                distance_pips = (current_price - position.open_price) * 100  # ติดลบถ้าราคาขึ้น
            
            analysis['current_drawdown_pips'] = distance_pips
            analysis['distance_from_entry'] = abs(distance_pips)
            
            # ประเมินระดับ drawdown
            if analysis['distance_from_entry'] >= self.emergency_drawdown_pips:
                analysis['drawdown_level'] = 'EMERGENCY'
                analysis['risk_score'] = 95
                analysis['recommended_action'] = 'IMMEDIATE_HEDGE'
                analysis['needs_hedge'] = True
            elif analysis['distance_from_entry'] >= self.critical_drawdown_pips:
                analysis['drawdown_level'] = 'CRITICAL'
                analysis['risk_score'] = 80
                analysis['recommended_action'] = 'URGENT_HEDGE'
                analysis['needs_hedge'] = True
            elif analysis['distance_from_entry'] >= self.drawdown_trigger_pips:
                analysis['drawdown_level'] = 'HIGH'
                analysis['risk_score'] = 60
                analysis['recommended_action'] = 'CONSIDER_HEDGE'
                analysis['needs_hedge'] = True
            else:
                analysis['drawdown_level'] = 'SAFE'
                analysis['risk_score'] = 20
                analysis['recommended_action'] = 'MONITOR'
            
            # สร้างคำแนะนำ hedge
            if analysis['needs_hedge']:
                analysis['hedge_suggestions'] = self.generate_hedge_suggestions(position, analysis)
            
            return analysis
            
        except Exception as e:
            self.log(f"Error analyzing drawdown: {str(e)}", "ERROR")
            return analysis

    def generate_hedge_suggestions(self, position: Position, analysis: dict) -> List[dict]:
        """สร้างคำแนะนำการ hedge"""
        suggestions = []
        
        try:
            distance = analysis['distance_from_entry']
            drawdown_level = analysis['drawdown_level']
            
            # Strategy 1: Immediate Hedge
            hedge_volume = self.calculate_hedge_volume(position, "IMMEDIATE")
            suggestions.append({
                'strategy': 'IMMEDIATE_HEDGE',
                'description': f'Hedge {hedge_volume:.2f} lots opposite direction immediately',
                'volume': hedge_volume,
                'expected_coverage': self.hedge_coverage_ratio,
                'recovery_potential': 'Medium',
                'risk_level': 'Low'
            })
            
            # Strategy 2: Smart Recovery (รอจังหวะ)
            if drawdown_level in ['HIGH', 'CRITICAL']:
                smart_volume = self.calculate_hedge_volume(position, "SMART_RECOVERY")
                suggestions.append({
                    'strategy': 'SMART_RECOVERY',
                    'description': f'Wait for reversal signal, then hedge {smart_volume:.2f} lots',
                    'volume': smart_volume,
                    'expected_coverage': self.hedge_coverage_ratio * 0.8,
                    'recovery_potential': 'High',
                    'risk_level': 'Medium'
                })
            
            # Strategy 3: Multi-Level Hedge
            if drawdown_level == 'EMERGENCY':
                level1_volume = position.volume * 0.6
                level2_volume = position.volume * 0.8
                suggestions.append({
                    'strategy': 'MULTI_LEVEL',
                    'description': f'Level 1: {level1_volume:.2f} lots now, Level 2: {level2_volume:.2f} lots at +50 pips',
                    'volume': level1_volume,
                    'expected_coverage': 1.4,
                    'recovery_potential': 'Very High',
                    'risk_level': 'High'
                })
            
            return suggestions
            
        except Exception as e:
            self.log(f"Error generating hedge suggestions: {str(e)}", "ERROR")
            return []

    def calculate_hedge_volume(self, position: Position, strategy: str) -> float:
        """คำนวณ volume สำหรับ hedge"""
        try:
            base_volume = position.volume
            
            if self.hedge_volume_calculation == "FIXED_RATIO":
                hedge_volume = base_volume * self.hedge_coverage_ratio
                
            elif self.hedge_volume_calculation == "DYNAMIC_RATIO":
                # ปรับ ratio ตามระยะห่างและสถานการณ์ - แก้ไข recursion
                # ดึงราคาปัจจุบันโดยตรงแทนการเรียก analyze_position_drawdown
                current_tick = mt5.symbol_info_tick(self.symbol)
                if current_tick:
                    current_price = current_tick.ask if position.type == "BUY" else current_tick.bid
                    
                    # คำนวณระยะห่างโดยตรง
                    if position.type == "BUY":
                        distance_pips = (position.open_price - current_price) * 100
                    else:  # SELL
                        distance_pips = (current_price - position.open_price) * 100
                    
                    distance = abs(distance_pips)
                    
                    # ปรับ ratio ตามระยะห่าง
                    if distance >= self.emergency_drawdown_pips:
                        ratio = self.hedge_coverage_ratio * 1.3  # เพิ่มมากขึ้น
                    elif distance >= self.critical_drawdown_pips:
                        ratio = self.hedge_coverage_ratio * 1.1
                    else:
                        ratio = self.hedge_coverage_ratio * 0.9
                else:
                    ratio = self.hedge_coverage_ratio
                
                hedge_volume = base_volume * ratio
                
            elif self.hedge_volume_calculation == "LOSS_BASED":
                # คำนวณจาก loss amount
                loss_amount = abs(position.profit)
                if loss_amount > 0:
                    # สมมติต้องการ hedge ให้ครอบคลุม 120% ของ loss
                    target_coverage = loss_amount * self.hedge_coverage_ratio
                    # ประมาณ pip value (ปรับตามโบรกเกอร์)
                    pip_value_per_lot = 100  # XAUUSD โดยประมาณ
                    hedge_volume = target_coverage / pip_value_per_lot
                else:
                    hedge_volume = base_volume * self.hedge_coverage_ratio
            else:
                # Default fallback
                hedge_volume = base_volume * self.hedge_coverage_ratio
            
            # ปรับตาม strategy
            if strategy == "SMART_RECOVERY":
                hedge_volume *= 0.8  # ลดลงเพราะรอจังหวะดี
            elif strategy == "MULTI_LEVEL":
                hedge_volume *= 0.6  # level แรก ใช้น้อยกว่า
            
            # จำกัดขอบเขต
            hedge_volume = max(self.min_hedge_volume, min(self.max_hedge_volume, hedge_volume))
            hedge_volume = round(hedge_volume, 2)
            
            return hedge_volume
            
        except Exception as e:
            self.log(f"Error calculating hedge volume: {str(e)}", "ERROR")
            return self.min_hedge_volume

    def execute_auto_hedge(self, position: Position, strategy: str = "IMMEDIATE") -> bool:
        """ดำเนินการ hedge อัตโนมัติ"""
        try:
            if not self.hedge_system_enabled:
                return False
            
            # ตรวจสอบว่ามี hedge อยู่แล้วหรือไม่
            if position.ticket in self.active_hedges:
                current_hedges = len(self.active_hedges[position.ticket])
                if current_hedges >= self.max_hedge_levels:
                    self.log(f"⚠️ Max hedge levels reached for position {position.ticket}")
                    return False
            
            # คำนวณ hedge volume
            hedge_volume = self.calculate_hedge_volume(position, strategy)
            
            # กำหนดทิศทางตรงข้าม
            hedge_type = mt5.ORDER_TYPE_SELL if position.type == "BUY" else mt5.ORDER_TYPE_BUY
            hedge_direction = "SELL" if position.type == "BUY" else "BUY"
            
            # สร้าง order request
            if self.filling_type is None:
                self.filling_type = self.detect_broker_filling_type()
            
            request = {
                "action": mt5.TRADE_ACTION_DEAL,
                "symbol": self.symbol,
                "volume": hedge_volume,
                "type": hedge_type,
                "deviation": 20,
                "magic": 123457,  # ใช้ magic number ต่างจาก trade ปกติ
                "comment": f"HG_{position.ticket}_{strategy[:4]}",
                "type_time": mt5.ORDER_TIME_GTC,
                "type_filling": self.filling_type,
            }
            
            # ส่ง order
            result = mt5.order_send(request)
            
            if result.retcode == mt5.TRADE_RETCODE_DONE:
                hedge_ticket = result.order
                
                # บันทึกการ hedge
                if position.ticket not in self.active_hedges:
                    self.active_hedges[position.ticket] = []
                
                self.active_hedges[position.ticket].append({
                    'hedge_ticket': hedge_ticket,
                    'hedge_volume': hedge_volume,
                    'hedge_type': hedge_direction,
                    'creation_time': datetime.now(),
                    'creation_price': result.price,
                    'strategy': strategy,
                    'level': len(self.active_hedges[position.ticket]) + 1
                })
                
                self.hedge_pairs[hedge_ticket] = position.ticket
                
                # อัพเดท statistics
                self.hedge_analytics['total_hedges_created'] += 1
                self.hedge_analytics['active_hedge_pairs'] += 1
                
                self.log(f"✅ Hedge created: {hedge_direction} {hedge_volume} lots for position {position.ticket}")
                self.log(f"   Strategy: {strategy}, Ticket: {hedge_ticket}")
                self.log(f"   Original: {position.type} {position.volume} lots @ {position.open_price}")
                
                return True
                
            else:
                self.log(f"❌ Hedge creation failed: {result.retcode}", "ERROR")
                return False
                
        except Exception as e:
            self.log(f"Error executing auto hedge: {str(e)}", "ERROR")
            return False

    def manage_existing_hedges(self):
        """จัดการ hedge pairs ที่มีอยู่"""
        if not self.active_hedges:
            return
        
        try:
            for original_ticket, hedge_list in list(self.active_hedges.items()):
                # หา original position
                original_pos = None
                for pos in self.positions:
                    if pos.ticket == original_ticket:
                        original_pos = pos
                        break
                
                if not original_pos:
                    # Original position ถูกปิดแล้ว ให้ปิด hedge ด้วย
                    self.close_orphaned_hedges(original_ticket, hedge_list)
                    continue
                
                # จัดการแต่ละ hedge
                for hedge_info in hedge_list[:]:  # ใช้ slice เพื่อป้องกัน modification error
                    hedge_ticket = hedge_info['hedge_ticket']
                    
                    # หา hedge position
                    hedge_pos = None
                    for pos in self.positions:
                        if pos.ticket == hedge_ticket:
                            hedge_pos = pos
                            break
                    
                    if not hedge_pos:
                        # Hedge ถูกปิดแล้ว ลบออกจาก tracking
                        hedge_list.remove(hedge_info)
                        if hedge_ticket in self.hedge_pairs:
                            del self.hedge_pairs[hedge_ticket]
                        continue
                    
                    # วิเคราะห์ว่าควรปิด hedge pair หรือไม่
                    should_close, reason = self.should_close_hedge_pair(original_pos, hedge_pos, hedge_info)
                    
                    if should_close:
                        success = self.close_hedge_pair(original_pos, hedge_pos, reason)
                        if success:
                            hedge_list.remove(hedge_info)
                            if hedge_ticket in self.hedge_pairs:
                                del self.hedge_pairs[hedge_ticket]
                
                # ลบ original ticket ถ้าไม่มี hedge เหลือ
                if not hedge_list:
                    del self.active_hedges[original_ticket]
                    
        except Exception as e:
            self.log(f"Error managing existing hedges: {str(e)}", "ERROR")

    def should_close_hedge_pair(self, original_pos: Position, hedge_pos: Position, hedge_info: dict) -> Tuple[bool, str]:
        """ตัดสินใจว่าควรปิด hedge pair หรือไม่"""
        try:
            # คำนวณกำไรรวม
            total_profit = original_pos.profit + hedge_pos.profit
            combined_volume = original_pos.volume + hedge_pos.volume
            avg_profit_per_lot = total_profit / combined_volume if combined_volume > 0 else 0
            
            # เงื่อนไข 1: กำไรรวมเกินเป้า
            target_profit = self.hedge_recovery_target / 100 * 1000 * combined_volume  # 2% of margin
            if total_profit >= target_profit:
                return True, f"Recovery target reached: ${total_profit:.2f} (target: ${target_profit:.2f})"
            
            # เงื่อนไข 2: Hedge กำไรดีพอและ original กลับมาใกล้เคียง
            hedge_profit_pct = (hedge_pos.profit_per_lot / 1000) * 100  # สมมติ margin 1000/lot
            original_loss_pct = (original_pos.profit_per_lot / 1000) * 100
            
            if (hedge_profit_pct >= self.hedge_min_profit_to_close and 
                original_loss_pct >= -5.0):  # original ขาดทุนไม่เกิน 5%
                return True, f"Hedge profitable & original recovered: HG +{hedge_profit_pct:.1f}%, Orig {original_loss_pct:.1f}%"
            
            # เงื่อนไข 3: Portfolio health ต่ำ และมีกำไรรวม
            if (self.portfolio_health < 40 and 
                total_profit > combined_volume * 20):  # กำไรรวม > $20/lot
                return True, f"Portfolio health emergency: ${total_profit:.2f} profit captured"
            
            # เงื่อนไข 4: เวลานานเกินไป และมีกำไรบ้าง
            hedge_age_hours = (datetime.now() - hedge_info['creation_time']).total_seconds() / 3600
            if (hedge_age_hours > 24 and total_profit > 0):
                return True, f"Long duration + positive: {hedge_age_hours:.1f}h, ${total_profit:.2f}"
            
            # เงื่อนไข 5: Market reversal แรง (เทคนิคขั้นสูง)
            if self.detect_market_reversal(original_pos, hedge_pos):
                return True, "Strong market reversal detected"
            
            return False, "Continue monitoring"
            
        except Exception as e:
            self.log(f"Error evaluating hedge pair: {str(e)}", "ERROR")
            return False, "Error in evaluation"

    
    def detect_market_reversal(self, original_pos: Position, hedge_pos: Position) -> bool:
        """ตรวจจับการเปลี่ยนทิศทางของตลาด"""
        try:
            # ดึงข้อมูลตลาดล่าสุด
            market_data = self.get_market_data()
            if market_data is None or len(market_data) < 5:
                return False
            
            # วิเคราะห์ momentum ล่าสุด
            last_5 = market_data.tail(5)
            
            # ตรวจสอบการเปลี่ยนทิศทาง
            if original_pos.type == "BUY":  # Original เป็น BUY ที่ติดลบ
                # ถ้าตลาดเริ่มขึ้นแรง (3/5 candles เป็นสีเขียว)
                green_count = last_5['is_green'].sum()
                avg_movement = last_5['movement'].mean()
                
                if green_count >= 3 and avg_movement > 0.5:  # เพิ่ม 'and'
                    return True
                    
            else:  # Original เป็น SELL ที่ติดลบ
                # ถ้าตลาดเริ่มลงแรง (3/5 candles เป็นสีแดง)
                red_count = 5 - last_5['is_green'].sum()
                avg_movement = last_5['movement'].mean()
                
                if red_count >= 3 and avg_movement > 0.5:  # เพิ่ม 'and'
                    return True
            
            return False
            
        except Exception as e:
            self.log(f"Error detecting reversal: {str(e)}", "ERROR")
            return False
    
    def close_hedge_pair(self, original_pos: Position, hedge_pos: Position, reason: str) -> bool:
        """ปิด hedge pair"""
        try:
            success_count = 0
            total_profit = original_pos.profit + hedge_pos.profit
            
            # ปิด original position ก่อน
            if self.close_position_smart(original_pos, f"Hedge pair close: {reason}"):
                success_count += 1
                time.sleep(0.5)
            
            # ปิด hedge position
            if self.close_position_smart(hedge_pos, f"Hedge pair close: {reason}"):
                success_count += 1
            
            if success_count == 2:
                # อัพเดท statistics
                self.hedge_analytics['successful_recoveries'] += 1
                self.hedge_analytics['total_recovery_profit'] += total_profit
                self.hedge_analytics['active_hedge_pairs'] -= 1
                
                self.log(f"✅ Hedge pair closed successfully!")
                self.log(f"   Original: {original_pos.ticket} ({original_pos.type} {original_pos.volume})")
                self.log(f"   Hedge: {hedge_pos.ticket} ({hedge_pos.type} {hedge_pos.volume})")
                self.log(f"   Total profit: ${total_profit:.2f}")
                self.log(f"   Reason: {reason}")
                
                return True
            else:
                self.log(f"❌ Partial hedge pair close: {success_count}/2 positions closed")
                return False
                
        except Exception as e:
            self.log(f"Error closing hedge pair: {str(e)}", "ERROR")
            return False

    def close_orphaned_hedges(self, original_ticket: int, hedge_list: List[dict]):
        """ปิด hedge ที่ original position หายไป"""
        try:
            for hedge_info in hedge_list:
                hedge_ticket = hedge_info['hedge_ticket']
                
                # หา hedge position
                hedge_pos = None
                for pos in self.positions:
                    if pos.ticket == hedge_ticket:
                        hedge_pos = pos
                        break
                
                if hedge_pos:
                    if self.close_position_smart(hedge_pos, f"Orphaned hedge (original {original_ticket} closed)"):
                        self.log(f"✅ Closed orphaned hedge {hedge_ticket}")
                        if hedge_ticket in self.hedge_pairs:
                            del self.hedge_pairs[hedge_ticket]
            
            # ลบออกจาก tracking
            if original_ticket in self.active_hedges:
                del self.active_hedges[original_ticket]
                
        except Exception as e:
            self.log(f"Error closing orphaned hedges: {str(e)}", "ERROR")

    def drawdown_management_system(self):
        """ระบบจัดการ drawdown หลัก - อัปเดตให้ใช้ Smart HG"""
        if not self.drawdown_management_enabled or not self.positions:
            return
        
        try:
            # 1. รัน Smart HG Management Cycle
            if self.smart_hg_enabled:
                self.smart_hg_management_cycle()
            else:
                # ใช้ระบบเก่าถ้า Smart HG ปิดอยู่
                for position in self.positions:
                    if position.ticket in self.hedge_pairs:
                        continue
                    
                    analysis = self.analyze_position_drawdown(position)
                    
                    if analysis['needs_hedge']:
                        self.log(f"⚠️ Drawdown detected: Position {position.ticket}")
                        self.log(f"   Distance: {analysis['distance_from_entry']:.0f} pips")
                        self.log(f"   Level: {analysis['drawdown_level']}")
                        
                        if analysis['drawdown_level'] in ['EMERGENCY', 'CRITICAL']:
                            self.execute_auto_hedge(position, "IMMEDIATE")
                        elif analysis['drawdown_level'] == 'HIGH':
                            if self.hedge_strategy == "SMART_RECOVERY":
                                if self.detect_market_reversal_opportunity(position):
                                    self.execute_auto_hedge(position, "SMART_RECOVERY")
                            else:
                                self.execute_auto_hedge(position, "IMMEDIATE")
            
            # 2. จัดการ hedge pairs ที่มีอยู่
            self.manage_existing_hedges()
            
        except Exception as e:
            self.log(f"Error in drawdown management: {str(e)}", "ERROR")

    def detect_market_reversal_opportunity(self, position: Position) -> bool:
        """ตรวจหาโอกาส reversal สำหรับ smart hedge"""
        try:
            market_data = self.get_market_data()
            if market_data is None or len(market_data) < 3:
                return False
            
            last_3 = market_data.tail(3)
            
            if position.type == "BUY":
                # ตลาดเริ่มกลับขึ้น
                green_count = last_3['is_green'].sum()
                if green_count >= 2:
                    return True
            else:
                # ตลาดเริ่มกลับลง
                red_count = 3 - last_3['is_green'].sum()
                if red_count >= 2:
                    return True
            
            return False
            
        except Exception as e:
            return False

    def get_hedge_analytics(self) -> dict:
        """สถิติระบบ hedge"""
        try:
            analytics = self.hedge_analytics.copy()
            
            # คำนวณประสิทธิภาพ
            total_hedges = analytics['total_hedges_created']
            successful_recoveries = analytics['successful_recoveries']
            
            if total_hedges > 0:
                analytics['hedge_effectiveness'] = (successful_recoveries / total_hedges) * 100
            
            if successful_recoveries > 0:
                analytics['avg_recovery_profit'] = analytics['total_recovery_profit'] / successful_recoveries
            else:
                analytics['avg_recovery_profit'] = 0.0
            
            # ข้อมูลปัจจุบัน
            analytics['positions_with_drawdown'] = 0
            analytics['positions_needing_hedge'] = 0
            
            for position in self.positions:
                if position.ticket not in self.hedge_pairs:  # ไม่นับ hedge positions
                    analysis = self.analyze_position_drawdown(position)
                    if analysis['distance_from_entry'] > 100:
                        analytics['positions_with_drawdown'] += 1
                    if analysis['needs_hedge']:
                        analytics['positions_needing_hedge'] += 1
            
            return analytics
            
        except Exception as e:
            self.log(f"Error getting hedge analytics: {str(e)}", "ERROR")
            return self.hedge_analytics

    def save_trading_state(self):
        """💾 บันทึกสถานะสำคัญของระบบ"""
        try:
            # ข้อมูลที่จะบันทึก
            state_data = {
                "timestamp": datetime.now().isoformat(),
                "version": "3.0",
                
                # Position tracking
                "position_tracker": self.position_tracker,
                "active_hedges": self.active_hedges,
                "hedge_pairs": self.hedge_pairs,
                
                # Statistics
                "daily_trades": self.daily_trades,
                "total_signals": self.total_signals,
                "successful_signals": self.successful_signals,
                "last_signal_time": self.last_signal_time.isoformat() if self.last_signal_time else None,
                
                # Smart router stats
                "total_redirects": self.total_redirects,
                "successful_redirects": self.successful_redirects,
                "redirect_profit_captured": self.redirect_profit_captured,
                "last_redirect_time": self.last_redirect_time.isoformat() if self.last_redirect_time else None,
                
                # Pair/Group closing stats
                "total_pair_closes": self.total_pair_closes,
                "successful_pair_closes": self.successful_pair_closes,
                "pair_profit_captured": self.pair_profit_captured,
                "total_group_closes": self.total_group_closes,
                "group_profit_captured": self.group_profit_captured,
                
                # Hedge analytics
                "hedge_analytics": self.hedge_analytics,
                
                # Portfolio info
                "portfolio_health": self.portfolio_health,
                
                # Settings (สำคัญ)
                "base_lot": self.base_lot,
                "smart_router_enabled": self.smart_router_enabled,
                "pair_closing_enabled": self.pair_closing_enabled,
                "hedge_system_enabled": self.hedge_system_enabled,
                "drawdown_management_enabled": self.drawdown_management_enabled
            }
            
            # บันทึกเป็น JSON
            with open(self.state_file, 'w', encoding='utf-8') as f:
                json.dump(state_data, f, ensure_ascii=False, indent=2)
            
            self.log(f"✅ Trading state saved to {self.state_file}")
            return True
            
        except Exception as e:
            self.log(f"❌ Error saving state: {str(e)}", "ERROR")
            return False

    def load_trading_state(self):
        """📂 โหลดสถานะที่บันทึกไว้"""
        try:
            if not os.path.exists(self.state_file):
                self.log(f"📝 No previous state found ({self.state_file})")
                return False
            
            with open(self.state_file, 'r', encoding='utf-8') as f:
                state_data = json.load(f)
            
            # ตรวจสอบ version
            if state_data.get("version") != "3.0":
                self.log("⚠️ Different version detected, loading basic data only", "WARNING")
            
            # Restore data
            self.position_tracker = state_data.get("position_tracker", {})
            self.active_hedges = state_data.get("active_hedges", {})
            self.hedge_pairs = state_data.get("hedge_pairs", {})
            
            # Statistics
            self.daily_trades = state_data.get("daily_trades", 0)
            self.total_signals = state_data.get("total_signals", 0)
            self.successful_signals = state_data.get("successful_signals", 0)
            
            # Parse datetime strings
            if state_data.get("last_signal_time"):
                self.last_signal_time = datetime.fromisoformat(state_data["last_signal_time"])
            
            # Smart router stats
            self.total_redirects = state_data.get("total_redirects", 0)
            self.successful_redirects = state_data.get("successful_redirects", 0)
            self.redirect_profit_captured = state_data.get("redirect_profit_captured", 0.0)
            
            if state_data.get("last_redirect_time"):
                self.last_redirect_time = datetime.fromisoformat(state_data["last_redirect_time"])
            
            # Pair/Group stats
            self.total_pair_closes = state_data.get("total_pair_closes", 0)
            self.successful_pair_closes = state_data.get("successful_pair_closes", 0)
            self.pair_profit_captured = state_data.get("pair_profit_captured", 0.0)
            self.total_group_closes = state_data.get("total_group_closes", 0)
            self.group_profit_captured = state_data.get("group_profit_captured", 0.0)
            
            # Hedge analytics
            if state_data.get("hedge_analytics"):
                self.hedge_analytics.update(state_data["hedge_analytics"])
            
            # Portfolio
            self.portfolio_health = state_data.get("portfolio_health", 100.0)
            
            # Settings
            self.base_lot = state_data.get("base_lot", self.base_lot)
            self.smart_router_enabled = state_data.get("smart_router_enabled", True)
            self.pair_closing_enabled = state_data.get("pair_closing_enabled", True)
            self.hedge_system_enabled = state_data.get("hedge_system_enabled", True)
            self.drawdown_management_enabled = state_data.get("drawdown_management_enabled", True)
            
            # แปลง position_tracker datetime strings กลับ
            self.restore_position_tracker_datetime()
            
            saved_time = state_data.get("timestamp", "Unknown")
            self.log(f"✅ Trading state loaded from {saved_time}")
            self.log(f"📊 Restored: {len(self.position_tracker)} position trackers")
            self.log(f"📊 Restored: {len(self.active_hedges)} hedge groups")
            self.log(f"📊 Stats: {self.total_signals} signals, {self.total_redirects} redirects")
            
            return True
            
        except Exception as e:
            self.log(f"❌ Error loading state: {str(e)}", "ERROR")
            return False

    def restore_position_tracker_datetime(self):
        """แปลง datetime strings ใน position_tracker กลับเป็น datetime objects"""
        try:
            for ticket, tracker in self.position_tracker.items():
                if isinstance(tracker.get('birth_time'), str):
                    tracker['birth_time'] = datetime.fromisoformat(tracker['birth_time'])
                    
            # ทำเช่นเดียวกันกับ active_hedges
            for original_ticket, hedge_list in self.active_hedges.items():
                for hedge_info in hedge_list:
                    if isinstance(hedge_info.get('creation_time'), str):
                        hedge_info['creation_time'] = datetime.fromisoformat(hedge_info['creation_time'])
                        
        except Exception as e:
            self.log(f"Error restoring datetime objects: {str(e)}", "ERROR")

    def backup_positions_data(self):
        """💾 Backup positions data (เป็น binary เพื่อความเร็ว)"""
        try:
            if not self.positions:
                return
            
            positions_data = {
                'positions': [pos.__dict__ for pos in self.positions],
                'buy_volume': self.buy_volume,
                'sell_volume': self.sell_volume,
                'timestamp': datetime.now(),
                'total_positions': len(self.positions)
            }
            
            with open(self.positions_file, 'wb') as f:
                pickle.dump(positions_data, f)
                
            self.log(f"📦 Positions backup: {len(self.positions)} positions saved")
            
        except Exception as e:
            self.log(f"Error backing up positions: {str(e)}", "ERROR")

    def restore_positions_reference(self):
        """📂 โหลดข้อมูล positions สำหรับอ้างอิง (ไม่ใช่การเทรดจริง)"""
        try:
            if not os.path.exists(self.positions_file):
                return None
            
            with open(self.positions_file, 'rb') as f:
                positions_data = pickle.load(f)
            
            backup_time = positions_data.get('timestamp', 'Unknown')
            total_positions = positions_data.get('total_positions', 0)
            
            self.log(f"📋 Reference positions available: {total_positions} from {backup_time}")
            return positions_data
            
        except Exception as e:
            self.log(f"Error loading positions reference: {str(e)}", "ERROR")
            return None

    def auto_save_state(self):
        """🔄 Auto-save ทุก 5 นาที"""
        try:
            # Save trading state
            self.save_trading_state()
            
            # Backup positions
            self.backup_positions_data()
            
            # Clean up old files (เก็บแค่ 7 วัน)
            self.cleanup_old_files()
            
        except Exception as e:
            self.log(f"Error in auto-save: {str(e)}", "ERROR")

    def cleanup_old_files(self):
        """🧹 ทำความสะอาดไฟล์เก่า"""
        try:
            # สร้างชื่อไฟล์แบบมี timestamp
            timestamp = datetime.now().strftime("%Y%m%d")
            
            # Archive ไฟล์ปัจจุบัน
            if os.path.exists(self.state_file):
                archive_name = f"trading_state_{timestamp}.json"
                if not os.path.exists(archive_name):
                    os.rename(self.state_file, archive_name)
                    self.log(f"📁 State archived as {archive_name}")
            
            # ลบไฟล์เก่าที่เก็บเกิน 7 วัน
            current_time = datetime.now()
            for filename in os.listdir('.'):
                if filename.startswith('trading_state_') and filename.endswith('.json'):
                    try:
                        file_date = datetime.strptime(filename[14:22], "%Y%m%d")
                        if (current_time - file_date).days > 7:
                            os.remove(filename)
                            self.log(f"🗑️ Removed old file: {filename}")
                    except:
                        continue
                        
        except Exception as e:
            self.log(f"Error cleaning up files: {str(e)}", "ERROR")

    def get_memory_status(self) -> dict:
        """📊 สถานะหน่วยความจำ"""
        try:
            status = {
                'position_trackers': len(self.position_tracker),
                'active_hedges': len(self.active_hedges),
                'hedge_pairs': len(self.hedge_pairs),
                'hourly_signals': len(self.hourly_signals),
                'has_saved_state': os.path.exists(self.state_file),
                'has_positions_backup': os.path.exists(self.positions_file),
                'last_save': 'Never'
            }
            
            if os.path.exists(self.state_file):
                mod_time = os.path.getmtime(self.state_file)
                status['last_save'] = datetime.fromtimestamp(mod_time).strftime("%H:%M:%S")
            
            return status
            
        except Exception as e:
            self.log(f"Error getting memory status: {str(e)}", "ERROR")
            return {}

    def emergency_state_recovery(self):
        """🚨 กู้คืนสถานะฉุกเฉิน"""
        try:
            self.log("🚨 EMERGENCY RECOVERY MODE", "WARNING")
            
            # พยายามโหลดจากไฟล์ backup
            success = self.load_trading_state()
            
            if success:
                self.log("✅ Emergency recovery successful")
                
                # ตรวจสอบและซิงค์กับ MT5
                if self.mt5_connected:
                    self.sync_with_mt5_positions()
                    
            else:
                self.log("❌ Emergency recovery failed - starting fresh", "ERROR")
                self.reset_to_defaults()
                
        except Exception as e:
            self.log(f"❌ Critical error in emergency recovery: {str(e)}", "ERROR")
            self.reset_to_defaults()

    def sync_with_mt5_positions(self):
        """🔄 ซิงค์ข้อมูลกับ positions จริงใน MT5"""
        try:
            if not self.mt5_connected:
                return
            
            # ดึง positions จริงจาก MT5
            mt5_positions = mt5.positions_get(symbol=self.symbol)
            if mt5_positions is None:
                mt5_positions = []
            
            mt5_tickets = {pos.ticket for pos in mt5_positions}
            tracked_tickets = set(self.position_tracker.keys())
            
            # ลบ tracker ที่ไม่มี position จริงแล้ว
            closed_tickets = tracked_tickets - mt5_tickets
            for ticket in closed_tickets:
                if str(ticket) in self.position_tracker:
                    del self.position_tracker[str(ticket)]
                elif int(ticket) in self.position_tracker:
                    del self.position_tracker[int(ticket)]
            
            # เพิ่ม tracker สำหรับ positions ใหม่
            new_tickets = mt5_tickets - tracked_tickets
            for pos in mt5_positions:
                if pos.ticket in new_tickets:
                    self.position_tracker[pos.ticket] = {
                        'birth_time': datetime.now(),
                        'initial_price': pos.price_open,
                        'max_profit': pos.profit,
                        'min_profit': pos.profit,
                        'role_history': ["UNKNOWN"],
                        'efficiency_history': ["fair"],
                        'peak_profit_per_lot': pos.profit / pos.volume if pos.volume > 0 else 0,
                        'contribution_score': 0.0,
                        'hold_score': 50,
                        'adaptive_target': self.profit_harvest_threshold
                    }
            
            self.log(f"🔄 Synced with MT5: {len(closed_tickets)} removed, {len(new_tickets)} added")
            
        except Exception as e:
            self.log(f"Error syncing with MT5: {str(e)}", "ERROR")

    def reset_to_defaults(self):
        """🔄 รีเซ็ตเป็นค่าเริ่มต้น"""
        try:
            self.position_tracker = {}
            self.active_hedges = {}
            self.hedge_pairs = {}
            self.hourly_signals = []
            
            # รีเซ็ต stats (เก็บแค่วันนี้)
            self.total_redirects = 0
            self.successful_redirects = 0
            self.redirect_profit_captured = 0.0
            self.last_redirect_time = None
            
            self.total_pair_closes = 0
            self.successful_pair_closes = 0
            self.pair_profit_captured = 0.0
            self.total_group_closes = 0
            self.group_profit_captured = 0.0
            
            self.portfolio_health = 100.0
            
            self.log("🔄 System reset to defaults")
            
        except Exception as e:
            self.log(f"Error resetting to defaults: {str(e)}", "ERROR")

    def analyze_hg_necessity(self, position: Position) -> dict:
        """🧠 วิเคราะห์ความจำเป็นในการออก HG แบบฉลาด"""
        try:
            analysis = {
                'should_hedge': False,
                'confidence_score': 0,
                'strategy': None,
                'volume_recommendation': 0.0,
                'timing_recommendation': 'IMMEDIATE',
                'risk_factors': [],
                'opportunity_factors': [],
                'decision_reasoning': []
            }
            
            # 1. Basic Loss Analysis
            loss_analysis = self.analyze_position_loss_severity(position)
            analysis['risk_factors'].extend(loss_analysis['factors'])
            
            # 2. Market Context Analysis
            market_context = self.analyze_market_context_for_hg(position)
            analysis['opportunity_factors'].extend(market_context['factors'])
            
            # 3. Portfolio Impact Analysis
            portfolio_impact = self.analyze_portfolio_impact_of_hg(position)
            
            # 4. Timing Analysis
            timing_analysis = self.analyze_hg_timing_opportunity(position)
            
            # 5. Pattern Recognition
            pattern_analysis = self.analyze_historical_hg_patterns(position)
            
            # 6. Calculate Composite Score
            composite_score = self.calculate_hg_composite_score(
                loss_analysis, market_context, portfolio_impact, 
                timing_analysis, pattern_analysis
            )
            
            analysis['confidence_score'] = composite_score['total_score']
            analysis['decision_reasoning'] = composite_score['reasoning']
            
            # 7. Final Decision
            if composite_score['total_score'] >= self.hg_decision_threshold:
                analysis['should_hedge'] = True
                analysis['strategy'] = self.select_optimal_hg_strategy(position, composite_score)
                analysis['volume_recommendation'] = self.calculate_smart_hg_volume(position, composite_score)
                analysis['timing_recommendation'] = timing_analysis.get('best_timing', 'IMMEDIATE')
            
            return analysis
            
        except Exception as e:
            self.log(f"Error analyzing HG necessity: {str(e)}", "ERROR")
            return analysis

    def analyze_position_loss_severity(self, position: Position) -> dict:
        """📉 วิเคราะห์ความรุนแรงของการขาดทุน"""
        try:
            analysis = {
                'severity_level': 'LOW',
                'loss_amount': abs(position.profit),
                'loss_percentage': 0,
                'time_in_loss': 0,
                'factors': [],
                'score': 0
            }
            
            loss_amount = abs(position.profit)
            
            # คำนวณ % loss
            if position.volume > 0:
                estimated_margin = position.volume * 1000
                analysis['loss_percentage'] = (loss_amount / estimated_margin) * 100
            
            # วิเคราะห์เวลาที่ติดลบ
            if position.ticket in self.position_tracker:
                birth_time = self.position_tracker[position.ticket]['birth_time']
                loss_duration = (datetime.now() - birth_time).total_seconds() / 3600
                analysis['time_in_loss'] = loss_duration
            
            # ประเมินความรุนแรง
            if loss_amount >= 500:
                analysis['severity_level'] = 'CRITICAL'
                analysis['score'] += 40
                analysis['factors'].append(f"Critical loss: ${loss_amount:.0f}")
            elif loss_amount >= 250:
                analysis['severity_level'] = 'HIGH'
                analysis['score'] += 30
                analysis['factors'].append(f"High loss: ${loss_amount:.0f}")
            elif loss_amount >= 100:
                analysis['severity_level'] = 'MEDIUM'
                analysis['score'] += 20
                analysis['factors'].append(f"Medium loss: ${loss_amount:.0f}")
            else:
                analysis['severity_level'] = 'LOW'
                analysis['score'] += 5
            
            # Bonus สำหรับ loss % สูง
            if analysis['loss_percentage'] > 20:
                analysis['score'] += 25
                analysis['factors'].append(f"High loss %: {analysis['loss_percentage']:.1f}%")
            elif analysis['loss_percentage'] > 10:
                analysis['score'] += 15
                analysis['factors'].append(f"Moderate loss %: {analysis['loss_percentage']:.1f}%")
            
            # Penalty สำหรับ loss เล็กน้อย
            if loss_amount < self.min_loss_threshold_for_hg:
                analysis['score'] = max(0, analysis['score'] - 20)
                analysis['factors'].append("Loss too small for HG")
            
            return analysis
            
        except Exception as e:
            self.log(f"Error analyzing loss severity: {str(e)}", "ERROR")
            return {'severity_level': 'LOW', 'score': 0, 'factors': []}

    def analyze_market_context_for_hg(self, position: Position) -> dict:
        """🌍 วิเคราะห์บริบทตลาดสำหรับการตัดสินใจ HG"""
        try:
            context = {
                'market_trend': 'NEUTRAL',
                'volatility_level': 'NORMAL',
                'momentum_strength': 0.5,
                'reversal_probability': 0.5,
                'factors': [],
                'score': 0
            }
            
            market_data = self.get_market_data()
            if market_data is None:
                return context
            
            # 1. Trend Analysis
            trend_strength = self.calculate_trend_strength(market_data)
            if trend_strength > 0.7:
                context['market_trend'] = 'STRONG_UP'
                context['score'] += 15
                context['factors'].append("Strong uptrend detected")
            elif trend_strength < 0.3:
                context['market_trend'] = 'STRONG_DOWN'
                context['score'] += 15
                context['factors'].append("Strong downtrend detected")
            else:
                context['market_trend'] = 'SIDEWAYS'
                context['score'] += 25  # Sideways ดีสำหรับ HG
                context['factors'].append("Sideways market - good for HG")
            
            # 2. Volatility Analysis
            if hasattr(self, 'recent_volatility'):
                if self.recent_volatility > 2.0:
                    context['volatility_level'] = 'HIGH'
                    context['score'] += 20
                    context['factors'].append("High volatility - HG opportunity")
                elif self.recent_volatility < 0.5:
                    context['volatility_level'] = 'LOW'
                    context['score'] += 5
                    context['factors'].append("Low volatility - limited HG benefit")
                else:
                    context['volatility_level'] = 'NORMAL'
                    context['score'] += 10
            
            # 3. Momentum vs Position Direction
            momentum = self.calculate_momentum_score(market_data)
            context['momentum_strength'] = momentum
            
            if position.type == "BUY" and momentum < 0.3:
                context['score'] += 20
                context['factors'].append("BUY against bearish momentum - HG recommended")
            elif position.type == "SELL" and momentum > 0.7:
                context['score'] += 20
                context['factors'].append("SELL against bullish momentum - HG recommended")
            
            # 4. Reversal Pattern Detection
            reversal_score = self.detect_reversal_patterns(market_data, position)
            context['reversal_probability'] = reversal_score
            if reversal_score > 0.7:
                context['score'] += 15
                context['factors'].append("High reversal probability detected")
            
            return context
            
        except Exception as e:
            self.log(f"Error analyzing market context for HG: {str(e)}", "ERROR")
            return context

    def analyze_portfolio_impact_of_hg(self, position: Position) -> dict:
        """💼 วิเคราะห์ผลกระทบต่อ portfolio จากการทำ HG"""
        try:
            impact = {
                'margin_impact': 'LOW',
                'balance_impact': 'NEUTRAL',
                'risk_reduction': 0,
                'recovery_potential': 0,
                'score': 0,
                'factors': []
            }
            
            # 1. Margin Usage Analysis
            account_info = mt5.account_info()
            if account_info and account_info.margin > 0:
                current_margin_level = (account_info.equity / account_info.margin) * 100
                
                # Estimate margin after HG
                hedge_volume = self.calculate_hedge_volume(position, "IMMEDIATE")
                estimated_additional_margin = hedge_volume * 1000  # ประมาณการ
                new_margin_level = (account_info.equity / (account_info.margin + estimated_additional_margin)) * 100
                
                if new_margin_level > 200:
                    impact['margin_impact'] = 'LOW'
                    impact['score'] += 15
                elif new_margin_level > 150:
                    impact['margin_impact'] = 'MEDIUM'
                    impact['score'] += 10
                else:
                    impact['margin_impact'] = 'HIGH'
                    impact['score'] += 0
                    impact['factors'].append(f"High margin impact: {new_margin_level:.0f}%")
            
            # 2. Portfolio Balance Impact
            total_volume = self.buy_volume + self.sell_volume
            if total_volume > 0:
                current_buy_ratio = self.buy_volume / total_volume
                
                # Calculate balance after HG
                if position.type == "BUY":
                    new_sell_volume = self.sell_volume + hedge_volume
                    new_buy_ratio = self.buy_volume / (total_volume + hedge_volume)
                else:
                    new_buy_volume = self.buy_volume + hedge_volume
                    new_buy_ratio = new_buy_volume / (total_volume + hedge_volume)
                
                current_imbalance = abs(current_buy_ratio - 0.5)
                new_imbalance = abs(new_buy_ratio - 0.5)
                
                if new_imbalance < current_imbalance:
                    impact['balance_impact'] = 'POSITIVE'
                    impact['score'] += 15
                    impact['factors'].append("HG improves portfolio balance")
                elif new_imbalance == current_imbalance:
                    impact['balance_impact'] = 'NEUTRAL'
                    impact['score'] += 5
                else:
                    impact['balance_impact'] = 'NEGATIVE'
                    impact['score'] -= 10
                    impact['factors'].append("HG worsens portfolio balance")
            
            # 3. Risk Reduction Calculation
            position_risk = abs(position.profit) / max(1, position.volume * 1000) * 100
            if position_risk > 15:
                impact['risk_reduction'] = 80
                impact['score'] += 25
                impact['factors'].append(f"High risk reduction: {position_risk:.1f}%")
            elif position_risk > 10:
                impact['risk_reduction'] = 60
                impact['score'] += 15
            else:
                impact['risk_reduction'] = 30
                impact['score'] += 5
            
            # 4. Recovery Potential
            if self.portfolio_health < 50:
                impact['recovery_potential'] = 80
                impact['score'] += 20
                impact['factors'].append("High recovery potential in weak portfolio")
            elif self.portfolio_health < 70:
                impact['recovery_potential'] = 60
                impact['score'] += 10
            else:
                impact['recovery_potential'] = 40
                impact['score'] += 5
            
            return impact
            
        except Exception as e:
            self.log(f"Error analyzing portfolio impact: {str(e)}", "ERROR")
            return impact

    def analyze_hg_timing_opportunity(self, position: Position) -> dict:
        """⏰ วิเคราะห์จังหวะเวลาที่เหมาะสมสำหรับ HG"""
        try:
            timing = {
                'best_timing': 'IMMEDIATE',
                'confidence': 0.5,
                'wait_recommendation': False,
                'optimal_delay_minutes': 0,
                'score': 0,
                'factors': []
            }
            
            # 1. Position Age Analysis
            age_hours = 0
            if position.ticket in self.position_tracker:
                birth_time = self.position_tracker[position.ticket]['birth_time']
                age_hours = (datetime.now() - birth_time).total_seconds() / 3600
            
            if age_hours < 1:
                timing['best_timing'] = 'WAIT'
                timing['wait_recommendation'] = True
                timing['optimal_delay_minutes'] = 30
                timing['score'] += 5
                timing['factors'].append("Position too young - wait for development")
            elif age_hours > 12:
                timing['best_timing'] = 'IMMEDIATE'
                timing['score'] += 20
                timing['factors'].append("Position mature - immediate HG recommended")
            else:
                timing['best_timing'] = 'IMMEDIATE'
                timing['score'] += 15
            
            # 2. Market Session Analysis
            current_hour = datetime.now().hour
            if 22 <= current_hour or current_hour <= 2:  # ตลาดหลัก
                timing['score'] += 15
                timing['factors'].append("Major market session - optimal HG timing")
            elif 7 <= current_hour <= 9 or 14 <= current_hour <= 16:  # ตลาดรอง
                timing['score'] += 10
                timing['factors'].append("Active market session - good HG timing")
            else:
                timing['score'] += 5
                timing['factors'].append("Quiet session - limited HG effectiveness")
            
            # 3. Recent HG Activity
            if hasattr(self, 'last_hedge_time'):
                if self.last_hedge_time:
                    minutes_since = (datetime.now() - self.last_hedge_time).total_seconds() / 60
                    if minutes_since < self.hg_cooldown_minutes:
                        timing['best_timing'] = 'WAIT'
                        timing['wait_recommendation'] = True
                        timing['optimal_delay_minutes'] = self.hg_cooldown_minutes - int(minutes_since)
                        timing['score'] -= 15
                        timing['factors'].append(f"HG cooldown: wait {timing['optimal_delay_minutes']} minutes")
            
            # 4. Market Volatility Timing
            if hasattr(self, 'recent_volatility'):
                if self.recent_volatility > 2.5:
                    timing['confidence'] = 0.8
                    timing['score'] += 10
                    timing['factors'].append("High volatility - excellent HG timing")
                elif self.recent_volatility < 0.3:
                    timing['confidence'] = 0.3
                    timing['score'] -= 5
                    timing['factors'].append("Low volatility - poor HG timing")
            
            # 5. Concurrent HG Limit Check
            active_hg_count = len(self.active_hedges)
            if active_hg_count >= self.hg_max_concurrent:
                timing['best_timing'] = 'WAIT'
                timing['wait_recommendation'] = True
                timing['score'] -= 20
                timing['factors'].append(f"Max concurrent HG reached: {active_hg_count}/{self.hg_max_concurrent}")
            
            timing['confidence'] = max(0.1, min(1.0, timing['score'] / 50))
            
            return timing
            
        except Exception as e:
            self.log(f"Error analyzing HG timing: {str(e)}", "ERROR")
            return timing

    def analyze_historical_hg_patterns(self, position: Position) -> dict:
        """📚 วิเคราะห์รูปแบบประสบการณ์ HG ในอดีต"""
        try:
            patterns = {
                'similar_situation_success_rate': 0.5,
                'recommended_strategy': 'IMMEDIATE',
                'confidence_from_history': 0.5,
                'score': 0,
                'factors': []
            }
            
            if not self.hg_pattern_learning:
                patterns['score'] = 10  # Base score
                return patterns
            
            # 1. Analyze similar positions from history
            similar_successes = 0
            similar_total = 0
            
            for record in self.hg_performance_history:
                # Check if similar situation
                if (record.get('original_type') == position.type and
                    abs(record.get('loss_amount', 0) - abs(position.profit)) < 100):
                    similar_total += 1
                    if record.get('final_result') == 'SUCCESS':
                        similar_successes += 1
            
            if similar_total > 0:
                patterns['similar_situation_success_rate'] = similar_successes / similar_total
                patterns['confidence_from_history'] = min(1.0, similar_total / 10)  # More confident with more data
                
                if patterns['similar_situation_success_rate'] > 0.7:
                    patterns['score'] += 20
                    patterns['factors'].append(f"High historical success: {patterns['similar_situation_success_rate']:.1%}")
                elif patterns['similar_situation_success_rate'] > 0.5:
                    patterns['score'] += 10
                    patterns['factors'].append(f"Moderate historical success: {patterns['similar_situation_success_rate']:.1%}")
                else:
                    patterns['score'] += 0
                    patterns['factors'].append(f"Low historical success: {patterns['similar_situation_success_rate']:.1%}")
            
            # 2. Strategy recommendation based on patterns
            if patterns['similar_situation_success_rate'] > 0.6:
                patterns['recommended_strategy'] = 'IMMEDIATE'
            else:
                patterns['recommended_strategy'] = 'SMART_RECOVERY'
            
            # 3. Check for known failure patterns
            current_market_data = self.get_market_data()
            if current_market_data is not None and self.avoid_bad_timing:
                if self.matches_failure_pattern(position, current_market_data):
                    patterns['score'] -= 15
                    patterns['factors'].append("Matches historical failure pattern")
            
            return patterns
            
        except Exception as e:
            self.log(f"Error analyzing HG patterns: {str(e)}", "ERROR")
            return patterns

    def calculate_hg_composite_score(self, loss_analysis: dict, market_context: dict, 
                                   portfolio_impact: dict, timing_analysis: dict, 
                                   pattern_analysis: dict) -> dict:
        """🧮 คำนวณคะแนนรวมสำหรับการตัดสินใจ HG"""
        try:
            composite = {
                'total_score': 0,
                'reasoning': [],
                'confidence_level': 'LOW',
                'risk_assessment': 'MEDIUM'
            }
            
            # Weight factors
            weights = {
                'loss_severity': 0.3,
                'market_context': self.market_context_weight,
                'portfolio_impact': 0.25,
                'timing': 0.15,
                'historical_patterns': 0.1
            }
            
            # Calculate weighted score
            scores = {
                'loss_severity': loss_analysis.get('score', 0),
                'market_context': market_context.get('score', 0),
                'portfolio_impact': portfolio_impact.get('score', 0),
                'timing': timing_analysis.get('score', 0),
                'historical_patterns': pattern_analysis.get('score', 0)
            }
            
            weighted_total = 0
            for factor, score in scores.items():
                weighted_score = score * weights[factor]
                weighted_total += weighted_score
                composite['reasoning'].append(f"{factor}: {score:.0f} pts (weight: {weights[factor]:.1%}) = {weighted_score:.1f}")
            
            composite['total_score'] = weighted_total
            
            # Determine confidence level
            if weighted_total >= 80:
                composite['confidence_level'] = 'VERY_HIGH'
                composite['risk_assessment'] = 'LOW'
            elif weighted_total >= 70:
                composite['confidence_level'] = 'HIGH'
                composite['risk_assessment'] = 'LOW'
            elif weighted_total >= 60:
                composite['confidence_level'] = 'MEDIUM'
                composite['risk_assessment'] = 'MEDIUM'
            elif weighted_total >= 40:
                composite['confidence_level'] = 'LOW'
                composite['risk_assessment'] = 'HIGH'
            else:
                composite['confidence_level'] = 'VERY_LOW'
                composite['risk_assessment'] = 'VERY_HIGH'
            
            # Add bonus/penalty factors
            if self.dynamic_risk_assessment:
                self.apply_dynamic_risk_adjustments(composite, portfolio_impact)
            
            return composite
            
        except Exception as e:
            self.log(f"Error calculating HG composite score: {str(e)}", "ERROR")
            return {'total_score': 0, 'reasoning': ['Error in calculation'], 'confidence_level': 'LOW'}

    def select_optimal_hg_strategy(self, position: Position, composite_score: dict) -> str:
        """🎯 เลือกกลยุทธ์ HG ที่เหมาะสมที่สุด"""
        try:
            if self.hg_strategy_selection == "AUTO_ADAPTIVE":
                score = composite_score['total_score']
                confidence = composite_score['confidence_level']
                
                if score >= 85 and confidence in ['HIGH', 'VERY_HIGH']:
                    return "IMMEDIATE_FULL"
                elif score >= 75:
                    return "IMMEDIATE"
                elif score >= 65:
                    return "SMART_RECOVERY"
                elif score >= 55:
                    return "PARTIAL_HEDGE"
                else:
                    return "WAIT_AND_MONITOR"
            
            else:
                # Use predefined strategy
                return self.hg_strategy_selection
                
        except Exception as e:
            self.log(f"Error selecting HG strategy: {str(e)}", "ERROR")
            return "IMMEDIATE"

    def calculate_smart_hg_volume(self, position: Position, composite_score: dict) -> float:
        """📐 คำนวณ volume HG อย่างชาญฉลาด"""
        try:
            base_volume = position.volume
            score = composite_score['total_score']
            confidence = composite_score['confidence_level']
            
            # Base ratio calculation
            if confidence == 'VERY_HIGH':
                ratio = 1.3  # 130% coverage
            elif confidence == 'HIGH':
                ratio = 1.2  # 120% coverage
            elif confidence == 'MEDIUM':
                ratio = 1.0  # 100% coverage
            else:
                ratio = 0.8  # 80% coverage
            
            # Adjust based on score
            if score >= 90:
                ratio *= 1.1
            elif score <= 60:
                ratio *= 0.9
            
            # Portfolio health adjustment
            if self.portfolio_health < 30:
                ratio *= 1.2  # More aggressive in crisis
            elif self.portfolio_health > 80:
                ratio *= 0.9  # More conservative when healthy
            
            # Calculate final volume
            hg_volume = base_volume * ratio
            
            # Apply limits
            hg_volume = max(self.min_hedge_volume, min(self.max_hedge_volume, hg_volume))
            hg_volume = round(hg_volume, 2)
            
            return hg_volume
            
        except Exception as e:
            self.log(f"Error calculating smart HG volume: {str(e)}", "ERROR")
            return self.min_hedge_volume

    def detect_reversal_patterns(self, market_data: pd.DataFrame, position: Position) -> float:
        """🔄 ตรวจจับรูปแบบการเปลี่ยนทิศทางของตลาด"""
        try:
            if market_data is None or len(market_data) < 5:
                return 0.5
            
            reversal_score = 0.0
            
            last_5 = market_data.tail(5)
            
            # 1. Candlestick pattern analysis
            if position.type == "BUY":
                # Look for bullish reversal patterns
                red_count = (last_5['is_green'] == False).sum()
                if red_count >= 3:  # Many red candles, potential reversal
                    reversal_score += 0.3
                
                # Check for hammer/doji patterns
                for idx, row in last_5.iterrows():
                    if row['body_ratio'] < 3 and row['total_range'] > 0.3:  # Small body, long wicks
                        reversal_score += 0.1
            
            else:  # SELL position
                # Look for bearish reversal patterns
                green_count = last_5['is_green'].sum()
                if green_count >= 3:  # Many green candles, potential reversal
                    reversal_score += 0.3
                
                # Check for shooting star/doji patterns
                for idx, row in last_5.iterrows():
                    if row['body_ratio'] < 3 and row['total_range'] > 0.3:
                        reversal_score += 0.1
            
            # 2. Momentum divergence
            momentum = self.calculate_momentum_score(market_data)
            if position.type == "BUY" and momentum > 0.6:
                reversal_score += 0.2
            elif position.type == "SELL" and momentum < 0.4:
                reversal_score += 0.2
            
            # 3. Volatility spike (often precedes reversal)
            if hasattr(self, 'recent_volatility') and self.recent_volatility > 2.0:
                reversal_score += 0.2
            
            return min(1.0, reversal_score)
            
        except Exception as e:
            self.log(f"Error detecting reversal patterns: {str(e)}", "ERROR")
            return 0.5

    def matches_failure_pattern(self, position: Position, market_data: pd.DataFrame) -> bool:
        """❌ ตรวจสอบว่าตรงกับรูปแบบที่เคยล้มเหลว"""
        try:
            if not self.hg_failure_analysis:
                return False
            
            current_conditions = {
                'position_type': position.type,
                'loss_range': self.categorize_loss_amount(abs(position.profit)),
                'market_trend': self.get_current_trend_category(market_data),
                'volatility_level': self.get_volatility_category()
            }
            
            # Check against known failure patterns
            for failure_pattern in self.hg_failure_analysis.get('patterns', []):
                match_count = 0
                total_factors = len(failure_pattern)
                
                for factor, value in failure_pattern.items():
                    if current_conditions.get(factor) == value:
                        match_count += 1
                
                # If 75% match, consider it a risky pattern
                if match_count / total_factors >= 0.75:
                    return True
            
            return False
            
        except Exception as e:
            self.log(f"Error checking failure patterns: {str(e)}", "ERROR")
            return False

    def apply_dynamic_risk_adjustments(self, composite: dict, portfolio_impact: dict):
        """⚖️ ปรับคะแนนตามความเสี่ยงแบบไดนามิก"""
        try:
            # Portfolio health penalty/bonus
            if self.portfolio_health < 30:
                composite['total_score'] += 10  # More aggressive when desperate
                composite['reasoning'].append("Emergency portfolio bonus: +10 pts")
            elif self.portfolio_health > 85:
                composite['total_score'] -= 5  # More conservative when healthy
                composite['reasoning'].append("Conservative health penalty: -5 pts")
            
            # Margin impact adjustment
            if portfolio_impact['margin_impact'] == 'HIGH':
                composite['total_score'] -= 15
                composite['reasoning'].append("High margin impact penalty: -15 pts")
            
            # Balance improvement bonus
            if portfolio_impact['balance_impact'] == 'POSITIVE':
                composite['total_score'] += 8
                composite['reasoning'].append("Balance improvement bonus: +8 pts")
            
            # Concurrent HG penalty
            active_hg_count = len(self.active_hedges)
            if active_hg_count > 2:
                penalty = (active_hg_count - 2) * 5
                composite['total_score'] -= penalty
                composite['reasoning'].append(f"Multiple HG penalty: -{penalty} pts")
                
        except Exception as e:
            self.log(f"Error applying risk adjustments: {str(e)}", "ERROR")

    def execute_smart_hg_decision(self, position: Position) -> bool:
        """🎯 ตัดสินใจและดำเนินการ HG อย่างชาญฉลาด"""
        try:
            if not self.smart_hg_enabled:
                return False
            
            # Analyze HG necessity
            hg_analysis = self.analyze_hg_necessity(position)
            
            if not hg_analysis['should_hedge']:
                self.log(f"🤔 HG Analysis: Not recommended for {position.ticket}")
                self.log(f"   Score: {hg_analysis['confidence_score']:.1f}/{self.hg_decision_threshold}")
                return False
            
            # Log decision reasoning
            self.log(f"🧠 SMART HG DECISION for Position {position.ticket}:")
            self.log(f"   Strategy: {hg_analysis['strategy']}")
            self.log(f"   Volume: {hg_analysis['volume_recommendation']:.2f} lots")
            self.log(f"   Timing: {hg_analysis['timing_recommendation']}")
            self.log(f"   Confidence: {hg_analysis['confidence_score']:.1f}/{self.hg_decision_threshold}")
            
            for reason in hg_analysis['decision_reasoning']:
                self.log(f"   • {reason}")
            
            # Execute based on timing recommendation
            if hg_analysis['timing_recommendation'] == 'IMMEDIATE':
                success = self.execute_auto_hedge(position, hg_analysis['strategy'])
                
                if success:
                    # Record success pattern
                    self.record_hg_decision(position, hg_analysis, 'EXECUTED')
                    self.last_hedge_time = datetime.now()
                    return True
                else:
                    # Record failure
                    self.record_hg_decision(position, hg_analysis, 'FAILED')
                    return False
            
            else:  # WAIT
                self.log(f"⏰ HG Decision: WAIT - {hg_analysis['timing_recommendation']}")
                self.record_hg_decision(position, hg_analysis, 'DELAYED')
                return False
                
        except Exception as e:
            self.log(f"Error in smart HG decision: {str(e)}", "ERROR")
            return False

    def record_hg_decision(self, position: Position, analysis: dict, outcome: str):
        """📝 บันทึกการตัดสินใจ HG เพื่อการเรียนรู้"""
        try:
            record = {
                'timestamp': datetime.now().isoformat(),
                'position_ticket': position.ticket,
                'position_type': position.type,
                'position_volume': position.volume,
                'loss_amount': abs(position.profit),
                'analysis_score': analysis['confidence_score'],
                'strategy_used': analysis.get('strategy'),
                'volume_used': analysis.get('volume_recommendation'),
                'outcome': outcome,
                'portfolio_health_at_time': self.portfolio_health,
                'market_conditions': self.get_current_market_snapshot()
            }
            
            self.hg_performance_history.append(record)
            
            # Keep only last 100 records
            if len(self.hg_performance_history) > 100:
                self.hg_performance_history = self.hg_performance_history[-100:]
                
        except Exception as e:
            self.log(f"Error recording HG decision: {str(e)}", "ERROR")

    def get_current_market_snapshot(self) -> dict:
        """📸 ถ่ายภาพสถานการณ์ตลาดปัจจุบัน"""
        try:
            market_data = self.get_market_data()
            
            if market_data is None:
                return {'trend': 'UNKNOWN', 'volatility': 'UNKNOWN'}
            
            return {
                'trend': self.get_current_trend_category(market_data),
                'volatility': self.get_volatility_category(),
                'momentum': self.calculate_momentum_score(market_data),
                'session': self.get_trading_session()
            }
            
        except Exception as e:
            return {'error': str(e)}

    def get_current_trend_category(self, market_data: pd.DataFrame) -> str:
        """📈 หาประเภทของเทรนด์ปัจจุบัน"""
        try:
            trend_strength = self.calculate_trend_strength(market_data)
            
            if trend_strength > 0.7:
                return 'STRONG_UP'
            elif trend_strength > 0.6:
                return 'MODERATE_UP'
            elif trend_strength < 0.3:
                return 'STRONG_DOWN'
            elif trend_strength < 0.4:
                return 'MODERATE_DOWN'
            else:
                return 'SIDEWAYS'
                
        except:
            return 'UNKNOWN'

    def get_volatility_category(self) -> str:
        """📊 หาประเภทของความผันผวน"""
        try:
            if hasattr(self, 'recent_volatility'):
                if self.recent_volatility > 2.5:
                    return 'VERY_HIGH'
                elif self.recent_volatility > 1.5:
                    return 'HIGH'
                elif self.recent_volatility < 0.5:
                    return 'LOW'
                else:
                    return 'NORMAL'
            return 'UNKNOWN'
        except:
            return 'UNKNOWN'

    def get_trading_session(self) -> str:
        """🕐 หาช่วงเวลาเทรดปัจจุบัน"""
        try:
            hour = datetime.now().hour
            
            if 22 <= hour or hour <= 2:
                return 'MAJOR'
            elif 7 <= hour <= 9:
                return 'ASIAN'
            elif 14 <= hour <= 16:
                return 'US'
            else:
                return 'QUIET'
                
        except:
            return 'UNKNOWN'

    def categorize_loss_amount(self, loss_amount: float) -> str:
        """💰 จัดหมวดหมู่จำนวนการขาดทุน"""
        if loss_amount < 50:
            return 'SMALL'
        elif loss_amount < 150:
            return 'MEDIUM'
        elif loss_amount < 300:
            return 'LARGE'
        else:
            return 'CRITICAL'

    def smart_hg_management_cycle(self):
        """🔄 รอบการจัดการ HG อัจฉริยะ"""
        if not self.smart_hg_enabled or not self.positions:
            return
        
        try:
            for position in self.positions:
                # ข้าม hedge positions
                if position.ticket in self.hedge_pairs:
                    continue
                
                # ข้ามถ้ามี HG อยู่แล้ว (ตรวจสอบขีดจำกัด)
                if position.ticket in self.active_hedges:
                    current_hedges = len(self.active_hedges[position.ticket])
                    if current_hedges >= self.max_hedge_levels:
                        continue
                
                # วิเคราะห์และตัดสินใจ
                if abs(position.profit) >= self.min_loss_threshold_for_hg:
                    self.execute_smart_hg_decision(position)
            
            # จัดการ HG ที่มีอยู่
            self.manage_existing_hedges()
            
        except Exception as e:
            self.log(f"Error in smart HG management cycle: {str(e)}", "ERROR")

    def get_smart_hg_analytics(self) -> dict:
        """📊 สถิติระบบ HG อัจฉริยะ"""
        try:
            analytics = {
                'smart_hg_enabled': self.smart_hg_enabled,
                'intelligence_level': self.hg_intelligence_level,
                'decision_threshold': self.hg_decision_threshold,
                'max_concurrent': self.hg_max_concurrent,
                'cooldown_minutes': self.hg_cooldown_minutes,
                
                'current_status': {
                    'active_hedges': len(self.active_hedges),
                    'total_hedge_pairs': sum(len(hedges) for hedges in self.active_hedges.values()),
                    'positions_eligible_for_hg': 0,
                    'positions_above_loss_threshold': 0
                },
                
                'performance_metrics': {
                    'total_decisions_made': len(self.hg_performance_history),
                    'successful_executions': 0,
                    'failed_executions': 0,
                    'delayed_decisions': 0,
                    'avg_decision_score': 0
                },
                
                'learning_data': {
                    'pattern_learning_enabled': self.hg_pattern_learning,
                    'success_patterns_identified': len(self.hg_success_patterns),
                    'failure_patterns_identified': len(self.hg_failure_analysis),
                    'market_reversal_detection': self.market_reversal_detection
                }
            }
            
            # นับ positions ที่เข้าเกณฑ์
            for position in self.positions:
                if position.ticket not in self.hedge_pairs:  # ไม่ใช่ hedge position
                    analytics['current_status']['positions_eligible_for_hg'] += 1
                    
                    if abs(position.profit) >= self.min_loss_threshold_for_hg:
                        analytics['current_status']['positions_above_loss_threshold'] += 1
            
            # คำนวณ performance metrics
            if self.hg_performance_history:
                executed = len([r for r in self.hg_performance_history if r['outcome'] == 'EXECUTED'])
                failed = len([r for r in self.hg_performance_history if r['outcome'] == 'FAILED'])
                delayed = len([r for r in self.hg_performance_history if r['outcome'] == 'DELAYED'])
                
                analytics['performance_metrics'].update({
                    'successful_executions': executed,
                    'failed_executions': failed,
                    'delayed_decisions': delayed,
                    'avg_decision_score': sum(r['analysis_score'] for r in self.hg_performance_history) / len(self.hg_performance_history)
                })
            
            return analytics
            
        except Exception as e:
            self.log(f"Error getting smart HG analytics: {str(e)}", "ERROR")
            return {}

class TradingGUI:
    def __init__(self):
        self.trading_system = TradingSystem()
        self.setup_gui()
        self.update_loop()

    def setup_gui(self):
        """Setup the main GUI"""
        self.root = tk.Tk()
        self.root.title("Modern AI Gold Grid Trading System v3.0")
        self.root.geometry("1500x900")
        self.root.configure(bg='#2b2b2b')
        
        # Style configuration
        style = ttk.Style()
        style.theme_use('clam')
        style.configure('Title.TLabel', font=('Arial', 12, 'bold'), background='#2b2b2b', foreground='white')
        style.configure('Status.TLabel', font=('Arial', 10), background='#2b2b2b', foreground='#00ff00')
        style.configure('Custom.TButton', font=('Arial', 9, 'bold'))
        
        self.create_header()
        self.create_control_panel()
        self.create_positions_frame()
        self.create_analytics_frame()
        self.create_log_frame()
        
        self.trading_system.root = self.root

    def create_header(self):
        """Create header with title and connection status"""
        header_frame = tk.Frame(self.root, bg='#2b2b2b', height=60)
        header_frame.pack(fill='x', padx=10, pady=5)
        header_frame.pack_propagate(False)
        
        title_label = ttk.Label(header_frame, text="🏆 Modern AI Gold Grid Trading System v3.0", 
                               style='Title.TLabel', font=('Arial', 16, 'bold'))
        title_label.pack(side='left', pady=15)
        
        self.connection_status = ttk.Label(header_frame, text="❌ Disconnected", 
                                          style='Status.TLabel', font=('Arial', 12, 'bold'))
        self.connection_status.pack(side='right', pady=15, padx=20)

    def create_control_panel(self):
        """Create control panel with buttons and status"""
        control_frame = tk.LabelFrame(self.root, text="🎮 Control Panel", 
                                     bg='#3b3b3b', fg='white', font=('Arial', 10, 'bold'))
        control_frame.pack(fill='x', padx=10, pady=5)
        
        # Connection buttons
        conn_frame = tk.Frame(control_frame, bg='#3b3b3b')
        conn_frame.pack(side='left', padx=10, pady=10)
        
        self.connect_btn = ttk.Button(conn_frame, text="🔌 Connect MT5", 
                                     command=self.connect_mt5, style='Custom.TButton')
        self.connect_btn.pack(side='left', padx=5)
        
        self.disconnect_btn = ttk.Button(conn_frame, text="🔌 Disconnect", 
                                        command=self.disconnect_mt5, style='Custom.TButton')
        self.disconnect_btn.pack(side='left', padx=5)
        
        # Trading buttons
        trade_frame = tk.Frame(control_frame, bg='#3b3b3b')
        trade_frame.pack(side='left', padx=20, pady=10)
        
        self.start_btn = ttk.Button(trade_frame, text="▶️ Start Trading", 
                                   command=self.start_trading, style='Custom.TButton')
        self.start_btn.pack(side='left', padx=5)
        
        self.stop_btn = ttk.Button(trade_frame, text="⏹️ Stop Trading", 
                                  command=self.stop_trading, style='Custom.TButton')
        self.stop_btn.pack(side='left', padx=5)
        
        # Portfolio info
        info_frame = tk.Frame(control_frame, bg='#3b3b3b')
        info_frame.pack(side='right', padx=10, pady=10)
        
        self.portfolio_label = ttk.Label(info_frame, text="💼 Portfolio Health: 100%", 
                                        style='Status.TLabel')
        self.portfolio_label.pack(side='top')
        
        self.volume_label = ttk.Label(info_frame, text="⚖️ Volume Balance: 0.00/0.00", 
                                     style='Status.TLabel')
        self.volume_label.pack(side='top')

    def create_positions_frame(self):
        """Create positions monitoring frame"""
        pos_frame = tk.LabelFrame(self.root, text="📊 Active Positions", 
                                 bg='#3b3b3b', fg='white', font=('Arial', 10, 'bold'))
        pos_frame.pack(fill='both', expand=True, padx=10, pady=5)
        
        # Create treeview for positions
        columns = ('Ticket', 'Type', 'Volume', 'Price', 'Current', 'Profit', '$/Lot', 'Role', 'Efficiency')
        self.positions_tree = ttk.Treeview(pos_frame, columns=columns, show='headings', height=10)
        
        # Configure columns
        for col in columns:
            self.positions_tree.heading(col, text=col)
            self.positions_tree.column(col, width=100, anchor='center')
        
        # Scrollbars
        v_scrollbar = ttk.Scrollbar(pos_frame, orient='vertical', command=self.positions_tree.yview)
        h_scrollbar = ttk.Scrollbar(pos_frame, orient='horizontal', command=self.positions_tree.xview)
        self.positions_tree.configure(yscrollcommand=v_scrollbar.set, xscrollcommand=h_scrollbar.set)
        
        # Pack treeview and scrollbars
        self.positions_tree.pack(side='left', fill='both', expand=True)
        v_scrollbar.pack(side='right', fill='y')
        h_scrollbar.pack(side='bottom', fill='x')

    def create_analytics_frame(self):
        """Create analytics and recommendations frame"""
        analytics_frame = tk.LabelFrame(self.root, text="📈 Analytics & Recommendations", 
                                       bg='#3b3b3b', fg='white', font=('Arial', 10, 'bold'))
        analytics_frame.pack(fill='x', padx=10, pady=5)
        
        # Stats frame
        stats_frame = tk.Frame(analytics_frame, bg='#3b3b3b')
        stats_frame.pack(side='left', fill='both', expand=True, padx=10, pady=10)
        
        self.stats_text = tk.Text(stats_frame, height=6, width=50, bg='#1e1e1e', fg='#00ff00', 
                                 font=('Consolas', 9))
        self.stats_text.pack(fill='both', expand=True)
        
        # Recommendations frame
        rec_frame = tk.Frame(analytics_frame, bg='#3b3b3b')
        rec_frame.pack(side='right', fill='both', expand=True, padx=10, pady=10)
        
        self.recommendations_text = tk.Text(rec_frame, height=6, width=50, bg='#1e1e1e', fg='#ffff00',
                                           font=('Consolas', 9))
        self.recommendations_text.pack(fill='both', expand=True)

    def create_log_frame(self):
        """Create log monitoring frame"""
        log_frame = tk.LabelFrame(self.root, text="📝 System Log", 
                                 bg='#3b3b3b', fg='white', font=('Arial', 10, 'bold'))
        log_frame.pack(fill='x', padx=10, pady=5)
        
        self.log_text = scrolledtext.ScrolledText(log_frame, height=8, bg='#1e1e1e', fg='#ffffff',
                                                 font=('Consolas', 9))
        self.log_text.pack(fill='both', expand=True, padx=5, pady=5)

    def connect_mt5(self):
        """Connect to MT5"""
        if self.trading_system.connect_mt5():
            self.connection_status.config(text="✅ Connected", foreground='#00ff00')
            messagebox.showinfo("Success", "Connected to MetaTrader 5")
        else:
            messagebox.showerror("Error", "Failed to connect to MetaTrader 5")

    def disconnect_mt5(self):
        """Disconnect from MT5"""
        self.stop_trading()
        self.trading_system.disconnect_mt5()
        self.connection_status.config(text="❌ Disconnected", foreground='#ff0000')

    def start_trading(self):
        """Start automated trading"""
        if not self.trading_system.mt5_connected:
            messagebox.showerror("Error", "Please connect to MT5 first")
            return
        
        if not self.trading_system.trading_active:
            self.trading_system.trading_active = True
            self.trading_thread = threading.Thread(target=self.trading_system.trading_loop, daemon=True)
            self.trading_thread.start()
            
            self.start_btn.config(state='disabled')
            self.stop_btn.config(state='normal')
            messagebox.showinfo("Success", "Trading started")

    def stop_trading(self):
        """Stop automated trading"""
        if self.trading_system.trading_active:
            self.trading_system.trading_active = False
            self.start_btn.config(state='normal')
            self.stop_btn.config(state='disabled')
            messagebox.showinfo("Success", "Trading stopped")

    def update_positions_display(self):
        """Update positions in the treeview"""
        try:
            # Clear existing items
            for item in self.positions_tree.get_children():
                self.positions_tree.delete(item)
            
            # Add current positions
            for pos in self.trading_system.positions:
                values = (
                    pos.ticket,
                    pos.type,
                    f"{pos.volume:.2f}",
                    f"{pos.open_price:.2f}",
                    f"{pos.current_price:.2f}",
                    f"${pos.profit:.2f}",
                    f"${pos.profit_per_lot:.2f}",
                    pos.role,
                    pos.efficiency
                )
                
                # Color coding based on efficiency
                if pos.efficiency == "excellent":
                    tag = "excellent"
                elif pos.efficiency == "good":
                    tag = "good"
                elif pos.efficiency == "fair":
                    tag = "fair"
                else:
                    tag = "poor"
                
                self.positions_tree.insert('', 'end', values=values, tags=(tag,))
            
            # Configure tags for color coding
            self.positions_tree.tag_configure("excellent", background="#004400")
            self.positions_tree.tag_configure("good", background="#003300")
            self.positions_tree.tag_configure("fair", background="#333300")
            self.positions_tree.tag_configure("poor", background="#440000")
            
        except Exception as e:
            print(f"Error updating positions display: {str(e)}")

    def update_analytics_display(self):
        """Update analytics with smart router information"""
        try:
            # Update statistics
            self.stats_text.delete(1.0, tk.END)
            
            smart_stats = self.trading_system.get_smart_management_stats()
            current_time = datetime.now().strftime("%H:%M:%S")
            
            # เพิ่มข้อมูล debug
            market_status = "Active" if self.trading_system.trading_active else "Stopped"
            last_signal = "Never"
            if self.trading_system.last_signal_time:
                seconds_ago = (datetime.now() - self.trading_system.last_signal_time).seconds
                last_signal = f"{seconds_ago}s ago"
            
            stats = f"""
⏰ REAL-TIME STATUS [{current_time}]:
Market Status: {market_status}
Last Signal: {last_signal}
Hourly Signals: {len(self.trading_system.hourly_signals)}/{self.trading_system.max_signals_per_hour}

🎯 TRADING STATISTICS:
Total Signals: {self.trading_system.total_signals}
Successful: {self.trading_system.successful_signals}
Success Rate: {(self.trading_system.successful_signals/max(1,self.trading_system.total_signals)*100):.1f}%
Daily Trades: {self.trading_system.daily_trades}/{self.trading_system.max_daily_trades}

🧠 SMART ROUTER STATS:
Total Redirects: {smart_stats.get('total_redirects', 0)}
Redirect Success: {smart_stats.get('redirect_success_rate', 0):.1f}%
Profit Captured: ${smart_stats.get('redirect_profit_captured', 0):.2f}
Redirect Ratio: {smart_stats.get('redirect_ratio', 0):.1f}%

💰 PORTFOLIO STATUS:
Active Positions: {len(self.trading_system.positions)}/{self.trading_system.max_positions}
Balance Ratio: {(self.trading_system.buy_volume/(self.trading_system.buy_volume+self.trading_system.sell_volume)*100) if (self.trading_system.buy_volume+self.trading_system.sell_volume) > 0 else 50:.1f}% BUY
Health Score: {self.trading_system.portfolio_health:.1f}%
            """
            
            self.stats_text.insert(tk.END, stats)
            
            # Update recommendations
            self.recommendations_text.delete(1.0, tk.END)
            recommendations = self.get_smart_router_recommendations(smart_stats)
            
            if recommendations:
                rec_text = "🧠 SMART ROUTER INSIGHTS:\n\n"
                for i, rec in enumerate(recommendations, 1):
                    rec_text += f"{i}. {rec}\n"
            else:
                rec_text = f"🧠 SYSTEM STATUS [{current_time}]:\n\n"
                if self.trading_system.trading_active:
                    rec_text += "✅ System running and monitoring market\n"
                    rec_text += "⏳ Waiting for signal conditions...\n"
                    rec_text += "📊 Analyzing M5 XAUUSD candles\n"
                else:
                    rec_text += "⏹️ Trading system stopped\n"
            
            self.recommendations_text.insert(tk.END, rec_text)
            
        except Exception as e:
            print(f"Error updating analytics display: {str(e)}")

    def get_smart_router_recommendations(self, smart_stats: dict) -> List[str]:
        """Generate smart router recommendations"""
        recommendations = []
        
        try:
            # Router performance analysis
            redirect_ratio = smart_stats.get('redirect_ratio', 0)
            redirect_success_rate = smart_stats.get('redirect_success_rate', 0)
            avg_hold_score = smart_stats.get('avg_hold_score', 50)
            
            if redirect_ratio > 30:
                recommendations.append(f"🔄 High redirect activity ({redirect_ratio:.1f}%) - Smart balance management active")
            
            if redirect_success_rate > 80 and smart_stats.get('total_redirects', 0) > 5:
                recommendations.append(f"✅ Excellent redirect success rate ({redirect_success_rate:.1f}%)")
            
            # Portfolio insights
            if avg_hold_score < 30:
                recommendations.append("📈 Low average hold score - Multiple positions ready for profit-taking")
            elif avg_hold_score > 70:
                recommendations.append("💪 High hold score - Portfolio in strong holding position")
            
            # Balance analysis
            total_volume = self.trading_system.buy_volume + self.trading_system.sell_volume
            if total_volume > 0:
                buy_ratio = self.trading_system.buy_volume / total_volume
                if abs(buy_ratio - 0.5) > 0.2:
                    recommendations.append(f"⚖️ Balance monitoring: {buy_ratio*100:.1f}% BUY - Router will optimize")
            
            # Profit capture insights
            profit_captured = smart_stats.get('redirect_profit_captured', 0)
            if profit_captured > 100:
                recommendations.append(f"💰 Router captured ${profit_captured:.2f} through smart redirects")
            
            # Position management
            ready_to_close = smart_stats.get('positions_ready_to_close', 0)
            if ready_to_close > 0:
                recommendations.append(f"🎯 {ready_to_close} positions ready for strategic closure")
            
            # System health
            if self.trading_system.portfolio_health < 40:
                recommendations.append("🚨 Portfolio health low - Smart system in protective mode")
            elif self.trading_system.portfolio_health > 80:
                recommendations.append("🌟 Excellent portfolio health - Smart system optimizing growth")
            
        except Exception as e:
            self.trading_system.log(f"Error generating router recommendations: {str(e)}", "ERROR")
        
        return recommendations

    def update_status_labels(self):
        """Update status labels"""
        try:
            self.portfolio_label.config(text=f"💼 Portfolio Health: {self.trading_system.portfolio_health:.1f}%")
            self.volume_label.config(text=f"⚖️ Volume Balance: {self.trading_system.buy_volume:.2f}/{self.trading_system.sell_volume:.2f}")
        except Exception as e:
            print(f"Error updating status labels: {str(e)}")

    def update_log_display(self):
        """Update log display with new messages"""
        try:
            while True:
                message = self.trading_system.log_queue.get_nowait()
                self.log_text.insert(tk.END, message + "\n")
                self.log_text.see(tk.END)
        except queue.Empty:
            pass

    def update_loop(self):
        """Main GUI update loop"""
        try:
            # Update all displays
            self.trading_system.update_positions()
            self.update_positions_display()
            self.update_analytics_display()
            self.update_status_labels()
            self.update_log_display()
            
        except Exception as e:
            print(f"GUI update error: {str(e)}")
        
        # Schedule next update
        self.root.after(2000, self.update_loop)  # Update every 2 seconds

    def run(self):
        """Start the GUI application"""
        self.trading_system.log("Modern AI Gold Grid Trading System v3.0 Started")
        self.trading_system.log("Ready for MT5 connection")
        self.root.mainloop()

def main():
    """Main application entry point"""
    try:
        app = TradingGUI()
        app.run()
    except Exception as e:
        print(f"Application error: {str(e)}")
        messagebox.showerror("Critical Error", f"Application failed to start: {str(e)}")

if __name__ == "__main__":
    main()