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
        
        # Enhanced Statistics
        self.hedge_orders_placed = 0
        self.exposure_warnings = 0
        self.sr_levels = []
        self.hedge_success_rate = 0.0
        self.total_hedge_profit = 0.0

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
        """Disconnect from MetaTrader 5"""
        if self.mt5_connected:
            mt5.shutdown()
            self.mt5_connected = False
            self.log("Disconnected from MT5")

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
        """คำนวณคะแนนความเหมาะสมในการปิด position เพื่อ redirect"""
        try:
            score = 0.0
            
            # 1. Profit score (40 points)
            if position.profit_per_lot >= self.min_profit_for_redirect_close:
                profit_ratio = position.profit_per_lot / self.profit_harvest_threshold
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
            if self.portfolio_health < 50 and position.profit > 0:
                score += 15
            
            # 5. Efficiency score (10 points)
            efficiency_points = {
                'excellent': 10,
                'good': 7,
                'fair': 4,
                'poor': 0
            }
            score += efficiency_points.get(position.efficiency, 0)
            
            return score
            
        except Exception as e:
            self.log(f"Error calculating redirect score: {str(e)}", "ERROR")
            return 0

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
            
            if ticket not in self.position_tracker:
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
        """ระบบจัดการ position อัจฉริยะ"""
        if not self.mt5_connected or not self.positions:
            return
        
        try:
            # ติดตามทุก position
            for position in self.positions:
                self.track_position_lifecycle(position)
            
            # ดำเนินการปิดแบบยืดหยุ่น
            self.execute_flexible_closes()
            
            # ทำความสะอาด tracker
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
        """Main trading loop with smart router and management"""
        self.log("🧠 Smart Trading System Started with Signal Router & Position Management")
        
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
                
                if market_data is not None:
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
                
                time.sleep(5)  # 5-second cycle
                
            except Exception as e:
                self.log(f"Error in trading loop: {str(e)}", "ERROR")
                time.sleep(10)
        
        self.log("🛑 Smart Trading System Stopped")

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

    def update_analytics_display(self):
        """Update analytics with smart router information"""
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
        self.portfolio_label.config(text=f"💼 Portfolio Health: {self.trading_system.portfolio_health:.1f}%")
        self.volume_label.config(text=f"⚖️ Volume Balance: {self.trading_system.buy_volume:.2f}/{self.trading_system.sell_volume:.2f}")

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