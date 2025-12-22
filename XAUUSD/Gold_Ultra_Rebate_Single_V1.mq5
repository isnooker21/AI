//+------------------------------------------------------------------+
//|                                Gold_Ultra_Rebate_Single_V1.mq5 |
//|                    Master Specification EA - Complete Version    |
//|                                                                  |
//+------------------------------------------------------------------+
#property copyright "Master Specification EA"
#property link      ""
#property version   "1.00"
#property strict

#include <Trade\Trade.mqh>

//--- Input Parameters
input group "=== Entry Settings ==="
input int             InpBreakoutPoints = 1;            // Breakout Points
input int             InpGridStep = 300;                // Grid Step (points)

input group "=== Central Brain: Multi-Tier Hostage System ==="
input int             InpHostageProfitPoints = 300;     // Points to qualify as Hostage
input double          InpMinMarginAnchor = 500.0;       // Min Margin % to keep Super Hostage
input double          InpHedgeRatioTarget = 0.85;       // Target Hedge Ratio (0.8 - 0.9)
input double          InpAmmoClearTarget = 0.10;        // Min Net Profit to execute Tier 3 clearing ($)
input int             InpVirtualTrailingPoints = 100;   // Virtual Trailing for Locked positions (points)
input double          InpStrategicNetTarget = 0.50;     // Strategic Clearing Target ($) - General
input double          InpMarginAlertLevel = 500.0;      // Margin Level % to trigger Recovery Mode
input double          InpGlobalProfit = 2.00;           // Global Reset Profit to Close ALL ($)
input double          InpBasketProfit = 5.00;           // Emergency Basket Profit ($)
input double          InpMaxLotRatio = 2.0;             // Max Lot Ratio between sides (Delta Limit)

input group "=== Time Filter ==="
input int             InpStopHour = 23;                 // Stop Trading Hour
input int             InpStopMinute = 55;                // Stop Trading Minute
input int             InpStartHour = 0;                  // Start Trading Hour
input int             InpStartMinute = 15;               // Start Trading Minute

input group "=== General Settings ==="
input int             InpMagicNumber = 123456;           // Magic Number
input string          InpTradeComment = "MasterEA";      // Trade Comment
input int             InpSlippage = 10;                  // Slippage (points)
input int             InpMaxRetries = 3;                 // Max Retries for Failed Orders
input int             InpRetryDelayMs = 1000;            // Retry Delay (milliseconds)

input group "=== Portfolio Balancing (Counter Grid) ==="
input int             InpCounterStep = 500;             // Counter-Trend Step (points)
input double          InpLotBalanceRatio = 1.5;         // Lot Ratio to trigger (e.g. 1.5)
input double          InpCounterLotMultiplier = 1.0;    // Multiplier for Gap filling (1.0 = full hedge)

//--- Global Variables
CTrade trade;

//--- Forward Declarations
void CentralOrderManager();
void CheckCounterBalancing();
void CheckRecoveryGrid();
void CheckInitialEntry(bool isNewBar);
void CheckCycleStatus();

datetime lastBarTime = 0;
datetime lastDebugPrint = 0;
double pointValue = 0;
bool cycleActive = false;              // Track if a cycle is active
bool IsProcessingTrade = false;        // Prevent multiple orders in same tick
datetime lastProcessingTime = 0;       // Track when processing flag was set
datetime lastCloseTime = 0;            // Track last time an order was closed
double peakProfitPool = 0;             // Track peak of the profit pool for adaptive release

// Stats for Strategic Monitor
double statsClearedProfit = 0;         // Total profit recovered today
int statsClearedTickets = 0;           // Total tickets cleared today
datetime lastStatsReset = 0;           // Last time stats were reset (daily)

datetime lastBuyLogTime = 0;          // Track last BUY distance log time
datetime lastSellLogTime = 0;         // Track last SELL distance log time
datetime lastBuyWaitLogTime = 0;      // Track last BUY waiting log time
datetime lastSellWaitLogTime = 0;     // Track last SELL waiting log time
datetime lastRecoveryBarTime = 0;     // Track last bar for recovery grid logging
datetime lastCounterBuyBarTime = 0;    // Track last counter buy bar
datetime lastCounterSellBarTime = 0;   // Track last counter sell bar

//+------------------------------------------------------------------+
//| Expert initialization function                                   |
//+------------------------------------------------------------------+
int OnInit()
{
   // Set trade parameters
   trade.SetExpertMagicNumber(InpMagicNumber);
   trade.SetDeviationInPoints(InpSlippage);
   trade.SetTypeFilling(ORDER_FILLING_IOC);
   trade.SetAsyncMode(false);
   
   // Get symbol properties
   pointValue = SymbolInfoDouble(_Symbol, SYMBOL_POINT);
   
   Print("=== Master Specification EA Initialized ===");
   Print("Symbol: ", _Symbol, " | Point: ", pointValue);
   Print("Breakout Points: ", InpBreakoutPoints, " | Grid Step: ", InpGridStep);
   Print("Global Offset: $", InpGlobalProfit, " | Basket Profit: $", InpBasketProfit);
   
   // Check if cycle is already active
   CheckCycleStatus();
   
   return(INIT_SUCCEEDED);
}

//+------------------------------------------------------------------+
//| Expert deinitialization function                                 |
//+------------------------------------------------------------------+
void OnDeinit(const int reason)
{
   Print("EA deinitialized. Reason: ", reason);
}

//+------------------------------------------------------------------+
//| Trade Transaction Event Handler                                  |
//| Resets IsProcessingTrade flag when trade completes              |
//+------------------------------------------------------------------+
void OnTradeTransaction(const MqlTradeTransaction& trans,
                       const MqlTradeRequest& request,
                       const MqlTradeResult& result)
{
   if(trans.type == TRADE_TRANSACTION_DEAL_ADD)
   {
      IsProcessingTrade = false;
   }
}

//+------------------------------------------------------------------+
//| Check if market is open and trading is allowed                  |
//+------------------------------------------------------------------+
bool IsMarketOpen()
{
   long tradeMode = SymbolInfoInteger(_Symbol, SYMBOL_TRADE_MODE);
   if(tradeMode != SYMBOL_TRADE_MODE_FULL)
      return false;
   
   if(!SymbolSelect(_Symbol, true))
      return false;
   
   double ask = SymbolInfoDouble(_Symbol, SYMBOL_ASK);
   double bid = SymbolInfoDouble(_Symbol, SYMBOL_BID);
   
   if(ask <= 0 || bid <= 0)
      return false;
   
   return true;
}

//+------------------------------------------------------------------+
//| Check current cycle status                                      |
//+------------------------------------------------------------------+
void CheckCycleStatus()
{
   int positionCount = GetPositionCount();
   
   if(positionCount > 0)
   {
      cycleActive = true;
      Print("=== CYCLE STATUS: ACTIVE ===");
      Print("Open Positions: ", positionCount);
   }
   else
   {
      cycleActive = false;
      Print("=== CYCLE STATUS: INACTIVE ===");
      Print("No open positions. Ready for new cycle.");
   }
}

//+------------------------------------------------------------------+
//| Get accurate commission for a position                           |
//+------------------------------------------------------------------+
double GetPositionCommission(ulong ticket)
{
   double commission = 0;
   if(HistorySelectByPosition(ticket))
   {
      int total = HistoryDealsTotal();
      for(int i = 0; i < total; i++)
      {
         ulong dealTicket = HistoryDealGetTicket(i);
         commission += HistoryDealGetDouble(dealTicket, DEAL_COMMISSION);
      }
   }
   return commission;
}

//+------------------------------------------------------------------+
//| Get position count for this EA (with type filter)               |
//+------------------------------------------------------------------+
int GetPositionCount(int type = -1)
{
   int count = 0;
   for(int i = PositionsTotal() - 1; i >= 0; i--)
   {
      ulong ticket = PositionGetTicket(i);
      if(ticket <= 0) continue;
      if(!PositionSelectByTicket(ticket)) continue;
      
      if(PositionGetString(POSITION_SYMBOL) != _Symbol) continue;
      if(PositionGetInteger(POSITION_MAGIC) != InpMagicNumber) continue;
      if(StringFind(PositionGetString(POSITION_COMMENT), "_Hedge") >= 0) continue;
      
      if(type != -1 && PositionGetInteger(POSITION_TYPE) != type) continue;
      
      count++;
   }
   return count;
}

//+------------------------------------------------------------------+
//| Get total lots for this EA (excluding hedges)                   |
//+------------------------------------------------------------------+
double GetTotalLots(int type)
{
   double totalLots = 0;
   for(int i = PositionsTotal() - 1; i >= 0; i--)
   {
      ulong ticket = PositionGetTicket(i);
      if(ticket <= 0) continue;
      if(!PositionSelectByTicket(ticket)) continue;
      
      if(PositionGetString(POSITION_SYMBOL) != _Symbol) continue;
      if(PositionGetInteger(POSITION_MAGIC) != InpMagicNumber) continue;
      if(StringFind(PositionGetString(POSITION_COMMENT), "_Hedge") >= 0) continue;
      
      if(PositionGetInteger(POSITION_TYPE) == type)
         totalLots += PositionGetDouble(POSITION_VOLUME);
   }
   return NormalizeDouble(totalLots, 2);
}

//+------------------------------------------------------------------+
//| Check if initial Buy position exists                            |
//+------------------------------------------------------------------+
bool HasInitialBuy()
{
   for(int i = PositionsTotal() - 1; i >= 0; i--)
   {
      ulong ticket = PositionGetTicket(i);
      if(ticket <= 0) continue;
      if(!PositionSelectByTicket(ticket)) continue;
      
      if(PositionGetString(POSITION_SYMBOL) != _Symbol) continue;
      if(PositionGetInteger(POSITION_MAGIC) != InpMagicNumber) continue;
      if(StringFind(PositionGetString(POSITION_COMMENT), "_Hedge") >= 0) continue;
      if(StringFind(PositionGetString(POSITION_COMMENT), "_Grid") >= 0) continue;
      
      if(PositionGetInteger(POSITION_TYPE) == POSITION_TYPE_BUY)
         return true;
   }
   return false;
}

//+------------------------------------------------------------------+
//| Check if initial Sell position exists                           |
//+------------------------------------------------------------------+
bool HasInitialSell()
{
   for(int i = PositionsTotal() - 1; i >= 0; i--)
   {
      ulong ticket = PositionGetTicket(i);
      if(ticket <= 0) continue;
      if(!PositionSelectByTicket(ticket)) continue;
      
      if(PositionGetString(POSITION_SYMBOL) != _Symbol) continue;
      if(PositionGetInteger(POSITION_MAGIC) != InpMagicNumber) continue;
      if(StringFind(PositionGetString(POSITION_COMMENT), "_Hedge") >= 0) continue;
      if(StringFind(PositionGetString(POSITION_COMMENT), "_Grid") >= 0) continue;
      
      if(PositionGetInteger(POSITION_TYPE) == POSITION_TYPE_SELL)
         return true;
   }
   return false;
}

//+------------------------------------------------------------------+
//| Get last position open time for given type                       |
//+------------------------------------------------------------------+
datetime GetLastPositionTime(ENUM_POSITION_TYPE posType)
{
   datetime lastTime = 0;
   for(int i = PositionsTotal() - 1; i >= 0; i--)
   {
      ulong ticket = PositionGetTicket(i);
      if(ticket <= 0) continue;
      if(!PositionSelectByTicket(ticket)) continue;
      
      if(PositionGetString(POSITION_SYMBOL) != _Symbol) continue;
      if(PositionGetInteger(POSITION_MAGIC) != InpMagicNumber) continue;
      if(StringFind(PositionGetString(POSITION_COMMENT), "_Hedge") >= 0) continue;
      
      if(PositionGetInteger(POSITION_TYPE) == posType)
      {
         datetime posTime = (datetime)PositionGetInteger(POSITION_TIME);
         if(posTime > lastTime)
            lastTime = posTime;
      }
   }
   return lastTime;
}

//+------------------------------------------------------------------+
//| Get nearest position price for given type                       |
//+------------------------------------------------------------------+
double GetNearestPositionPrice(ENUM_POSITION_TYPE posType, double currentPrice)
{
   double nearestPrice = 0;
   double minDistance = -1;
   
   for(int i = PositionsTotal() - 1; i >= 0; i--)
   {
      ulong ticket = PositionGetTicket(i);
      if(ticket <= 0) continue;
      if(!PositionSelectByTicket(ticket)) continue;
      
      if(PositionGetString(POSITION_SYMBOL) != _Symbol) continue;
      if(PositionGetInteger(POSITION_MAGIC) != InpMagicNumber) continue;
      if(StringFind(PositionGetString(POSITION_COMMENT), "_Hedge") >= 0) continue;
      
      if(PositionGetInteger(POSITION_TYPE) == posType)
      {
         double openPrice = PositionGetDouble(POSITION_PRICE_OPEN);
         double distance = MathAbs(currentPrice - openPrice);
         
         if(minDistance < 0 || distance < minDistance)
         {
            minDistance = distance;
            nearestPrice = openPrice;
         }
      }
   }
   return nearestPrice;
}

//+------------------------------------------------------------------+
//| Get last position price for given type                          |
//| For BUY: Returns LOWEST price                                   |
//| For SELL: Returns HIGHEST price                                 |
//+------------------------------------------------------------------+
double GetLastPositionPrice(ENUM_POSITION_TYPE posType, string commentFilter = "")
{
   double referencePrice = 0;
   bool firstFound = false;
   
   for(int i = PositionsTotal() - 1; i >= 0; i--)
   {
      ulong ticket = PositionGetTicket(i);
      if(ticket <= 0) continue;
      if(!PositionSelectByTicket(ticket)) continue;
      
      if(PositionGetString(POSITION_SYMBOL) != _Symbol) continue;
      if(PositionGetInteger(POSITION_MAGIC) != InpMagicNumber) continue;
      if(StringFind(PositionGetString(POSITION_COMMENT), "_Hedge") >= 0) continue;
      
      if(commentFilter != "" && StringFind(PositionGetString(POSITION_COMMENT), commentFilter) < 0)
         continue;
      
      if(PositionGetInteger(POSITION_TYPE) == posType)
      {
         double price = PositionGetDouble(POSITION_PRICE_OPEN);
         
         if(!firstFound)
         {
            referencePrice = price;
            firstFound = true;
         }
         else
         {
            // For BUY: Get LOWEST price (for averaging down)
            if(posType == POSITION_TYPE_BUY)
            {
               if(price < referencePrice)
                  referencePrice = price;
            }
            // For SELL: Get HIGHEST price (for averaging up)
            else
            {
               if(price > referencePrice)
                  referencePrice = price;
            }
         }
      }
   }
   
   return referencePrice;
}

//+------------------------------------------------------------------+
//| Get average price for given type                                 |
//+------------------------------------------------------------------+
double GetAveragePrice(ENUM_POSITION_TYPE posType)
{
   double totalOpenPrice = 0;
   double totalVolume = 0;
   for(int i = PositionsTotal() - 1; i >= 0; i--)
   {
      ulong ticket = PositionGetTicket(i);
      if(!PositionSelectByTicket(ticket)) continue;
      if(PositionGetString(POSITION_SYMBOL) != _Symbol || PositionGetInteger(POSITION_MAGIC) != InpMagicNumber) continue;
      if(StringFind(PositionGetString(POSITION_COMMENT), "_Hedge") >= 0) continue;
      
      if(PositionGetInteger(POSITION_TYPE) == posType)
      {
         double volume = PositionGetDouble(POSITION_VOLUME);
         totalOpenPrice += PositionGetDouble(POSITION_PRICE_OPEN) * volume;
         totalVolume += volume;
      }
   }
   return (totalVolume > 0) ? (totalOpenPrice / totalVolume) : 0;
}

//+------------------------------------------------------------------+
//| Get actual last opened price (by time) for spacing               |
//+------------------------------------------------------------------+
double GetActualLastPrice(ENUM_POSITION_TYPE posType, string commentFilter = "")
{
   datetime lastTime = 0;
   double lastPrice = 0;
   for(int i = PositionsTotal() - 1; i >= 0; i--)
   {
      ulong ticket = PositionGetTicket(i);
      if(!PositionSelectByTicket(ticket)) continue;
      if(PositionGetString(POSITION_SYMBOL) != _Symbol || PositionGetInteger(POSITION_MAGIC) != InpMagicNumber) continue;
      if(commentFilter != "" && StringFind(PositionGetString(POSITION_COMMENT), commentFilter) < 0) continue;
      
      if(PositionGetInteger(POSITION_TYPE) == posType)
      {
         datetime posTime = (datetime)PositionGetInteger(POSITION_TIME);
         if(posTime > lastTime)
         {
            lastTime = posTime;
            lastPrice = PositionGetDouble(POSITION_PRICE_OPEN);
         }
      }
   }
   return lastPrice;
}

//+------------------------------------------------------------------+
//| Expert tick function                                             |
//+------------------------------------------------------------------+
void OnTick()
{
   // Flag Safety: Reset IsProcessingTrade after 10 seconds
   if(IsProcessingTrade && TimeCurrent() - lastProcessingTime >= 10)
   {
      IsProcessingTrade = false;
      Print("⚠ Flag Safety: IsProcessingTrade reset after 10 seconds");
   }
   
   // Time Filter: Skip trading during Market Rollover (23:55 - 00:15)
   MqlDateTime dt;
   TimeToStruct(TimeCurrent(), dt);
   int currentHour = dt.hour;
   int currentMinute = dt.min;
   
   bool isRolloverTime = false;
   if(currentHour == InpStopHour && currentMinute >= InpStopMinute)
      isRolloverTime = true;
   else if(currentHour == InpStartHour && currentMinute < InpStartMinute)
      isRolloverTime = true;
   
   if(isRolloverTime)
      return;
   
   // Check if market is open
   if(!IsMarketOpen())
   {
      static datetime lastClosedPrint = 0;
      if(TimeCurrent() - lastClosedPrint >= 60)
      {
         Print("Market is CLOSED - Skipping tick");
         lastClosedPrint = TimeCurrent();
      }
      return;
   }
   
   // Check for new bar
   datetime currentBarTime = iTime(_Symbol, PERIOD_M5, 0);
   bool isNewBar = (currentBarTime != lastBarTime);
   if(isNewBar)
      lastBarTime = currentBarTime;
   
   // Main trading logic - CENTRAL BRAIN CONTROL
   CentralOrderManager();       // Decision maker for all closures & balancing
   CheckRecoveryGrid();         // Grid recovery (Defensive & Offensive)
   CheckInitialEntry(isNewBar); // Initial entry (only if no cycle)
}

//+------------------------------------------------------------------+
//| Central Order Manager (Adaptive Multi-Strategy Clearing)         |
//| Strategies: Grand Reset | Dual-Track Shaving | Smart Recycle     |
//+------------------------------------------------------------------+
void CentralOrderManager()
{
   if(GetPositionCount() == 0) {
      Comment(""); // Clear dashboard
      peakProfitPool = 0;
      return;
   }

   // --- INITIALIZATION & STATS ---
   double totalNetPL = 0;
   double totalBuyLots = 0, totalSellLots = 0;
   double totalBuyPL = 0, totalSellPL = 0;
   double marginLevel = AccountInfoDouble(ACCOUNT_MARGIN_LEVEL);
   
   // SAFETY VALVE: If Margin is critical, force emergency clearing
   bool isMarginCritical = (marginLevel > 0 && marginLevel < InpMarginAlertLevel);
   
   // Reset daily stats if new day
   MqlDateTime today;
   TimeToStruct(TimeCurrent(), today);
   if(today.day != lastStatsReset) {
      statsClearedProfit = 0;
      statsClearedTickets = 0;
      lastStatsReset = (datetime)today.day;
   }
   
   // CONFLICT CHECK: Validate input parameters
   if(InpGlobalProfit <= InpStrategicNetTarget)
   {
      Print("⚠ WARNING: InpGlobalProfit ($", InpGlobalProfit, ") should be > InpStrategicNetTarget ($", InpStrategicNetTarget, ")");
   }

   struct PosData {
      ulong ticket;
      double pl;
      double vol;
      double openPrice;
      ENUM_POSITION_TYPE type;
      int tier; // 1: Anchor, 2: Hedge, 3: Ammo, 4: Loser
      double dist; // Distance from current price
   };
   PosData positions[];
   int posIdx = 0;

   double ask = SymbolInfoDouble(_Symbol, SYMBOL_ASK);
   double bid = SymbolInfoDouble(_Symbol, SYMBOL_BID);

   for(int i = PositionsTotal() - 1; i >= 0; i--)
   {
      ulong ticket = PositionGetTicket(i);
      if(!PositionSelectByTicket(ticket)) continue;
      if(PositionGetString(POSITION_SYMBOL) != _Symbol || PositionGetInteger(POSITION_MAGIC) != InpMagicNumber) continue;
      if(StringFind(PositionGetString(POSITION_COMMENT), "_Hedge") >= 0) continue;
      
      double vol = PositionGetDouble(POSITION_VOLUME);
      double pl = PositionGetDouble(POSITION_PROFIT) + PositionGetDouble(POSITION_SWAP) + GetPositionCommission(ticket);
      double openPrice = PositionGetDouble(POSITION_PRICE_OPEN);
      ENUM_POSITION_TYPE type = (ENUM_POSITION_TYPE)PositionGetInteger(POSITION_TYPE);
      
      totalNetPL += pl;
      ArrayResize(positions, posIdx + 1);
      positions[posIdx].ticket = ticket;
      positions[posIdx].pl = pl;
      positions[posIdx].vol = vol;
      positions[posIdx].openPrice = openPrice;
      positions[posIdx].type = type;
      positions[posIdx].tier = (pl > 0) ? 3 : 4;
      positions[posIdx].dist = (type == POSITION_TYPE_BUY) ? MathAbs(bid - openPrice) : MathAbs(ask - openPrice);

      if(type == POSITION_TYPE_BUY) { totalBuyLots += vol; totalBuyPL += pl; }
      else { totalSellLots += vol; totalSellPL += pl; }
      posIdx++;
   }

   // --- 1. THE GRAND RESET STRATEGY (Overrides ALL locks including Anchor) ---
   if(totalNetPL >= InpGlobalProfit || isMarginCritical)
   {
      string reason = (totalNetPL >= InpGlobalProfit) ? "Target Reached" : "Margin Critical";
      Print("=== [Strategy: GRAND RESET] ", reason, "! Closing ALL (including Anchors). ===");
      for(int i=0; i<posIdx; i++) {
         double pl = positions[i].pl;
         if(trade.PositionClose(positions[i].ticket)) {
            statsClearedProfit += pl;
            statsClearedTickets++;
         }
      }
      lastCloseTime = TimeCurrent();
      CheckCycleStatus();
      return;
   }

   // --- IDENTIFY ANCHORS & AMMO POOL ---
   ulong anchorBuy = 0, anchorSell = 0;
   double minB = DBL_MAX, maxS = 0;
   double anchorPLSum = 0;

   for(int i=0; i<posIdx; i++) {
      if(positions[i].pl > 0) {
         if(positions[i].type == POSITION_TYPE_BUY && positions[i].openPrice < minB) { minB = positions[i].openPrice; anchorBuy = positions[i].ticket; }
         if(positions[i].type == POSITION_TYPE_SELL && positions[i].openPrice > maxS) { maxS = positions[i].openPrice; anchorSell = positions[i].ticket; }
      }
   }
   
   for(int i=0; i<posIdx; i++) {
      if(positions[i].ticket == anchorBuy || positions[i].ticket == anchorSell) {
         positions[i].tier = 1;
         anchorPLSum += positions[i].pl;
      }
   }

   // --- 4. SMART HOSTAGE RECYCLING ---
   double totalLoserPL = 0;
   for(int i=0; i<posIdx; i++) if(positions[i].pl < 0) totalLoserPL += positions[i].pl;

   if(anchorPLSum + totalLoserPL >= 0.10) {
      bool hugeAnchor = false;
      if(anchorBuy > 0) { 
         PositionSelectByTicket(anchorBuy); 
         if((bid - PositionGetDouble(POSITION_PRICE_OPEN))/pointValue > 500) hugeAnchor = true; 
      }
      if(!hugeAnchor && anchorSell > 0) { 
         PositionSelectByTicket(anchorSell); 
         if((PositionGetDouble(POSITION_PRICE_OPEN) - ask)/pointValue > 500) hugeAnchor = true; 
      }

      if(hugeAnchor) {
         Print("=== [Strategy: Smart Recycle] Anchors can cover all losers. Closing Cycle. ===");
         for(int i=0; i<posIdx; i++) {
            double pl = positions[i].pl;
            if(trade.PositionClose(positions[i].ticket)) {
               statsClearedProfit += pl;
               statsClearedTickets++;
            }
         }
         lastCloseTime = TimeCurrent();
         CheckCycleStatus();
         return;
      }
   }

   // --- 3. WORST-TICKET SHAVING (Shave only 0.01 Lot from worst loser) ---
   // STRICT SEPARATION: Anchor (Tier 1) is NEVER included in Ammo Pool
   double ammoPool = 0;
   ulong ammoTickets[];
   int ammoCount = 0;
   for(int i=0; i<posIdx; i++) {
      if(positions[i].pl > 0 && positions[i].tier != 1) {
         // EXCLUDE TIER 1 (ANCHOR) - Hard Lock separation
         ammoPool += positions[i].pl;
         ArrayResize(ammoTickets, ammoCount + 1);
         ammoTickets[ammoCount++] = positions[i].ticket;
      }
   }

   // Find worst loser (most negative PL)
   ulong worstLoserTicket = 0;
   double worstPL = 0;
   double worstVol = 0;
   for(int i=0; i<posIdx; i++) {
      if(positions[i].pl < 0 && positions[i].pl < worstPL) {
         worstPL = positions[i].pl;
         worstLoserTicket = positions[i].ticket;
         worstVol = positions[i].vol;
      }
   }

   // Shave 0.01 Lot from worst loser if we have enough profit
   if(worstLoserTicket > 0 && ammoPool >= 0.10 && worstVol >= 0.02)
   {
      double lotToShave = 0.01; // Fixed 0.01 Lot shaving
      double plPerLot = MathAbs(worstPL / worstVol);
      double requiredProfit = lotToShave * plPerLot + 0.01; // Buffer for slippage
      
      if(ammoPool >= requiredProfit)
      {
         Print("=== [Strategy: Worst-Ticket Shaving] Shaving 0.01 Lot from #", worstLoserTicket, " ===");
         for(int i=0; i<ammoCount; i++) trade.PositionClose(ammoTickets[i]);
         trade.PositionClosePartial(worstLoserTicket, lotToShave);
         statsClearedProfit += ammoPool; 
         statsClearedTickets += ammoCount;
         lastCloseTime = TimeCurrent();
         CheckCycleStatus();
         return;
      }
   }

   // --- DASHBOARD (Strategic Monitor) ---
   double baseLot = CalculateLotSize();
   double distanceToReset = InpGlobalProfit - totalNetPL;
   string activeStr = (isMarginCritical) ? "EMERGENCY CLEARING" : ((totalNetPL >= InpGlobalProfit * 0.8) ? "Grand Reset Imminent" : "Worst-Ticket Shaving");
   string dashboard = "=== STRATEGIC BRAIN MONITOR ===\n";
   dashboard += "Current Base Lot: " + DoubleToString(baseLot, 2) + (baseLot == 0 ? " [BLOCKED]" : "") + "\n";
   dashboard += "Distance to Grand Reset: $" + DoubleToString(distanceToReset, 2) + "\n";
   dashboard += "Active Strategy: " + activeStr + "\n";
   dashboard += "Cleared Today: " + IntegerToString(statsClearedTickets) + " Tiks ($" + DoubleToString(statsClearedProfit, 2) + ")\n";
   dashboard += "---------------------------------\n";
   dashboard += "Ammo Pool: $" + DoubleToString(ammoPool, 2) + " | Anchor PL: $" + DoubleToString(anchorPLSum, 2) + "\n";
   dashboard += "Margin Level: " + DoubleToString(marginLevel, 2) + "%" + (isMarginCritical ? " [CRITICAL]" : "") + "\n";
   dashboard += "Total Net P/L: $" + DoubleToString(totalNetPL, 2) + "\n";
   Comment(dashboard);
}

//+------------------------------------------------------------------+
//| Directional Hedge Balancing (Sell High / Buy Low)                |
//| Bridges the lot gap and addresses extreme distances              |
//+------------------------------------------------------------------+
void CheckCounterBalancing()
{
   if(IsProcessingTrade) return;
   if(GetPositionCount() == 0) return;
   
   // MARGIN SAFETY: Stop opening new trades if margin is critical
   double marginLevel = AccountInfoDouble(ACCOUNT_MARGIN_LEVEL);
   if(marginLevel > 0 && marginLevel < InpMarginAlertLevel)
   {
      return; // Let Clearing Logic handle it
   }

   double totalBuyLots = GetTotalLots(POSITION_TYPE_BUY);
   double totalSellLots = GetTotalLots(POSITION_TYPE_SELL);
   double ask = SymbolInfoDouble(_Symbol, SYMBOL_ASK);
   double bid = SymbolInfoDouble(_Symbol, SYMBOL_BID);
   datetime currentM5Bar = iTime(_Symbol, PERIOD_M5, 0);

   // Find Target Loser Price for distance-based entry
   ulong worstBuyTicket = 0, worstSellTicket = 0;
   double worstBuyPL = 0, worstSellPL = 0;
   for(int i = PositionsTotal() - 1; i >= 0; i--) {
      ulong t = PositionGetTicket(i);
      if(!PositionSelectByTicket(t) || PositionGetInteger(POSITION_MAGIC) != InpMagicNumber) continue;
      double pl = PositionGetDouble(POSITION_PROFIT) + PositionGetDouble(POSITION_SWAP);
      if(PositionGetInteger(POSITION_TYPE) == POSITION_TYPE_BUY && pl < worstBuyPL) { worstBuyPL = pl; worstBuyTicket = t; }
      if(PositionGetInteger(POSITION_TYPE) == POSITION_TYPE_SELL && pl < worstSellPL) { worstSellPL = pl; worstSellTicket = t; }
   }
   
   ulong targetTicket = (worstBuyPL < worstSellPL) ? worstBuyTicket : worstSellTicket;
   double targetOpenPrice = 0;
   if(targetTicket > 0) { PositionSelectByTicket(targetTicket); targetOpenPrice = PositionGetDouble(POSITION_PRICE_OPEN); }

   // --- CASE 1: Heavy BUY (or Price far from Buy) -> Open Counter SELL (Sell High) ---
   if(totalBuyLots > totalSellLots || (targetTicket > 0 && PositionGetInteger(POSITION_TYPE) == POSITION_TYPE_BUY && bid > targetOpenPrice + InpCounterStep * pointValue))
   {
      double avgBuyPrice = GetAveragePrice(POSITION_TYPE_BUY);
      double lastCounterSell = GetActualLastPrice(POSITION_TYPE_SELL, "_Counter");
      
      // Condition: Sell High (Bid > Avg Buy) AND Spacing
      if(bid > avgBuyPrice && (lastCounterSell == 0 || bid >= lastCounterSell + (InpCounterStep * pointValue)))
      {
         if(lastCounterSellBarTime < currentM5Bar)
         {
            double lotGap = totalBuyLots - totalSellLots;
            if(lotGap < 0) lotGap = CalculateLotSize(); // If triggered by distance but lot is balanced
            double counterLot = NormalizeDouble(lotGap * InpCounterLotMultiplier, 2);
            if(counterLot < SymbolInfoDouble(_Symbol, SYMBOL_VOLUME_MIN)) counterLot = SymbolInfoDouble(_Symbol, SYMBOL_VOLUME_MIN);

            Print("=== [Central Brain: Counter] Aggressive SELL High triggered ===");
            if(!IsLotRatioSafe(POSITION_TYPE_SELL, counterLot)) { Print("⚠ Counter SELL skipped: Ratio would exceed limit."); return; }
            IsProcessingTrade = true;
            lastProcessingTime = TimeCurrent();
            if(TradeWithRetry(ORDER_TYPE_SELL, counterLot, bid, 0, 0, "_Counter"))
               lastCounterSellBarTime = currentM5Bar;
            else 
               IsProcessingTrade = false;
         }
      }
   }
   // --- CASE 2: Heavy SELL (or Price far from Sell) -> Open Counter BUY (Buy Low) ---
   else if(totalSellLots > totalBuyLots || (targetTicket > 0 && PositionGetInteger(POSITION_TYPE) == POSITION_TYPE_SELL && ask < targetOpenPrice - InpCounterStep * pointValue))
   {
      double avgSellPrice = GetAveragePrice(POSITION_TYPE_SELL);
      double lastCounterBuy = GetActualLastPrice(POSITION_TYPE_BUY, "_Counter");
      
      // Condition: Buy Low (Ask < Avg Sell) AND Spacing
      if(ask < avgSellPrice && (lastCounterBuy == 0 || ask <= lastCounterBuy - (InpCounterStep * pointValue)))
      {
         if(lastCounterBuyBarTime < currentM5Bar)
         {
            double lotGap = totalSellLots - totalBuyLots;
            if(lotGap < 0) lotGap = CalculateLotSize(); // If triggered by distance
            double counterLot = NormalizeDouble(lotGap * InpCounterLotMultiplier, 2);
            if(counterLot < SymbolInfoDouble(_Symbol, SYMBOL_VOLUME_MIN)) counterLot = SymbolInfoDouble(_Symbol, SYMBOL_VOLUME_MIN);

            Print("=== [Central Brain: Counter] Aggressive BUY Low triggered ===");
            if(!IsLotRatioSafe(POSITION_TYPE_BUY, counterLot)) { Print("⚠ Counter BUY skipped: Ratio would exceed limit."); return; }
            IsProcessingTrade = true;
            lastProcessingTime = TimeCurrent();
            if(TradeWithRetry(ORDER_TYPE_BUY, counterLot, ask, 0, 0, "_Counter"))
               lastCounterBuyBarTime = currentM5Bar;
            else 
               IsProcessingTrade = false;
         }
      }
   }
}

//+------------------------------------------------------------------+
//| Check and Execute Initial Entry                                 |
//| Only runs when GetPositionCount() == 0                          |
//| BUY and SELL can trigger independently                          |
//+------------------------------------------------------------------+
void CheckInitialEntry(bool isNewBar)
{
   // Prevent multiple orders in same tick
   if(IsProcessingTrade)
      return;
   
   // Check if order is pending/in progress
   if(trade.ResultRetcode() == TRADE_RETCODE_PLACED || trade.ResultRetcode() == TRADE_RETCODE_DONE_PARTIAL)
      return;
   
   // MARGIN SAFETY: Stop opening new initial entries if margin is critical
   double marginLevel = AccountInfoDouble(ACCOUNT_MARGIN_LEVEL);
   if(marginLevel > 0 && marginLevel < InpMarginAlertLevel)
   {
      return; // Let Clearing Logic handle it
   }
   
   // Get current counts for each side (excluding hedges)
   int buyCount = GetPositionCount(POSITION_TYPE_BUY);
   int sellCount = GetPositionCount(POSITION_TYPE_SELL);
   
   // Get current prices
   double ask = SymbolInfoDouble(_Symbol, SYMBOL_ASK);
   double bid = SymbolInfoDouble(_Symbol, SYMBOL_BID);
   
   // Get previous candle data (Candle[1]) - M5 timeframe
   double high1 = iHigh(_Symbol, PERIOD_M5, 1);
   double low1 = iLow(_Symbol, PERIOD_M5, 1);
   
   // Calculate breakout levels
   double buyBreakout = high1 + (InpBreakoutPoints * pointValue);
   double sellBreakout = low1 - (InpBreakoutPoints * pointValue);
   
   // BUY Logic: If NO BUY positions exist
   if(buyCount == 0 && ask > buyBreakout)
   {
      double lotSize = CalculateLotSize(POSITION_TYPE_BUY); // Use dynamic lot based on balance
      if(lotSize > 0 && IsLotRatioSafe(POSITION_TYPE_BUY, lotSize))
      {
         Print("Checking Entry: Ask=", ask, ", High[1]=", high1);
         Print("  BUY Triggered! Breakout: ", buyBreakout);
         
         IsProcessingTrade = true;
         lastProcessingTime = TimeCurrent();
         
         // NO Take Profit - will be closed by offsetting or basket profit
         bool result = TradeWithRetry(ORDER_TYPE_BUY, lotSize, ask, 0, 0, "_Initial_BUY");
         
         IsProcessingTrade = false;
         
         if(result)
         {
            cycleActive = true;
            Print("=== CYCLE STARTED: Initial BUY Entry ===");
            Print("Price: ", ask, " | Breakout: ", buyBreakout, " | High[1]: ", high1);
            Print("Lot Size: ", lotSize, " | NO Take Profit");
         }
         else
         {
            Print("✗ BUY Entry FAILED: Ask=", ask, " | Breakout=", buyBreakout);
         }
      }
   }
   
   // SELL Logic: If NO SELL positions exist
   if(sellCount == 0 && bid < sellBreakout)
   {
      double lotSize = CalculateLotSize(POSITION_TYPE_SELL); // Use dynamic lot based on balance
      if(lotSize > 0 && IsLotRatioSafe(POSITION_TYPE_SELL, lotSize))
      {
         Print("Checking Entry: Bid=", bid, ", Low[1]=", low1);
         Print("  SELL Triggered! Breakout: ", sellBreakout);
         
         IsProcessingTrade = true;
         lastProcessingTime = TimeCurrent();
         
         // NO Take Profit - will be closed by offsetting or basket profit
         bool result = TradeWithRetry(ORDER_TYPE_SELL, lotSize, bid, 0, 0, "_Initial_SELL");
         
         IsProcessingTrade = false;
         
         if(result)
         {
            cycleActive = true;
            Print("=== CYCLE STARTED: Initial SELL Entry ===");
            Print("Price: ", bid, " | Breakout: ", sellBreakout, " | Low[1]: ", low1);
            Print("Lot Size: ", lotSize, " | NO Take Profit");
         }
         else
         {
            Print("✗ SELL Entry FAILED: Bid=", bid, " | Breakout=", sellBreakout);
         }
      }
   }
}

//+------------------------------------------------------------------+
//| Check Recovery Grid (Trend-Following Snowball Strategy)          |
//| Defensive: Against trend, scaling distance, reversal trigger     |
//| Offensive: With trend, fixed distance, trend following trigger   |
//+------------------------------------------------------------------+
void CheckRecoveryGrid()
{
   if(PositionsTotal() <= 0) 
   {
      cycleActive = false;
      return;
   }

   // MARGIN SAFETY: Stop opening new recovery trades if margin is critical
   double marginLevel = AccountInfoDouble(ACCOUNT_MARGIN_LEVEL);
   if(marginLevel > 0 && marginLevel < InpMarginAlertLevel)
   {
      return; // Let Clearing Logic handle it
   }

   int totalBuyCount = GetPositionCount(POSITION_TYPE_BUY);
   int totalSellCount = GetPositionCount(POSITION_TYPE_SELL);
   
   if(totalBuyCount <= 0 && totalSellCount <= 0)
   {
      cycleActive = false;
      return; 
   }
   
   if(IsProcessingTrade) return;
   if(trade.ResultRetcode() == TRADE_RETCODE_PLACED || trade.ResultRetcode() == TRADE_RETCODE_DONE_PARTIAL) return;

   // Prices and Candle Data
   double ask = SymbolInfoDouble(_Symbol, SYMBOL_ASK);
   double bid = SymbolInfoDouble(_Symbol, SYMBOL_BID);
   double high1 = iHigh(_Symbol, PERIOD_M5, 1);
   double low1 = iLow(_Symbol, PERIOD_M5, 1);
   double open1 = iOpen(_Symbol, PERIOD_M5, 1);
   double close1 = iClose(_Symbol, PERIOD_M5, 1);
   bool isGreenBar = (close1 > open1);
   bool isRedBar = (close1 < open1);
   datetime currentM5Bar = iTime(_Symbol, PERIOD_M5, 0);

   // --- BUY SIDE ANALYSIS ---
   if(totalBuyCount > 0)
   {
      datetime lastBuyTime = GetLastPositionTime(POSITION_TYPE_BUY);
      if(lastBuyTime < currentM5Bar) // 1 Bar 1 Trade
      {
         double lastBuyPrice = GetLastPositionPrice(POSITION_TYPE_BUY);
         
         // 1. Defensive Recovery (Against trend - Price is falling)
         double defensiveStep = InpGridStep;
         if(totalBuyCount >= 6) defensiveStep = InpGridStep + 500;
         else if(totalBuyCount >= 3) defensiveStep = InpGridStep + 200;
         defensiveStep = MathMax(defensiveStep, 150.0);
         
         double buyDefensiveTarget = lastBuyPrice - (defensiveStep * pointValue);
         
         // 2. Offensive Snowball (With trend - Price is rising)
         double offensiveStep = MathMax(InpGridStep, 200.0); // Standard step
         double buyOffensiveTarget = lastBuyPrice + (offensiveStep * pointValue);

         // Check Defensive
         if(ask <= buyDefensiveTarget)
         {
            if(isGreenBar && ask > high1) // Reversal Trigger
            {
               if(OpenGridTrade(ORDER_TYPE_BUY, ask, "BUY Recovery (Defensive)", totalBuyCount, defensiveStep)) return;
            }
            else if(TimeCurrent() - lastBuyWaitLogTime >= 60)
            {
               Print("WAITING - BUY Recovery (Defensive) at target but waiting for Reversal signal... (Ask=", ask, ", Step=", defensiveStep, ")");
               lastBuyWaitLogTime = TimeCurrent();
            }
         }
         // Check Offensive
         else if(ask >= buyOffensiveTarget)
         {
            // Minimum Spacing Rule (Sideways Protection)
            double nearestBuy = GetNearestPositionPrice(POSITION_TYPE_BUY, ask);
            double minSpacing = MathMax(200.0, InpGridStep * 0.6) * pointValue;
            
            if(nearestBuy > 0 && MathAbs(ask - nearestBuy) < minSpacing) 
               return; // Skip if too close to any existing BUY

            if(isGreenBar && ask > high1) // Trend Signal
            {
               if(OpenGridTrade(ORDER_TYPE_BUY, ask, "BUY Snowball (Offensive)", totalBuyCount, offensiveStep)) return;
            }
         }
      }
   }

   // --- SELL SIDE ANALYSIS ---
   if(totalSellCount > 0)
   {
      datetime lastSellTime = GetLastPositionTime(POSITION_TYPE_SELL);
      if(lastSellTime < currentM5Bar) // 1 Bar 1 Trade
      {
         double lastSellPrice = GetLastPositionPrice(POSITION_TYPE_SELL);
         
         // 1. Defensive Recovery (Against trend - Price is rising)
         double defensiveStep = InpGridStep;
         if(totalSellCount >= 6) defensiveStep = InpGridStep + 500;
         else if(totalSellCount >= 3) defensiveStep = InpGridStep + 200;
         defensiveStep = MathMax(defensiveStep, 150.0);
         
         double sellDefensiveTarget = lastSellPrice + (defensiveStep * pointValue);
         
         // 2. Offensive Snowball (With trend - Price is falling)
         double offensiveStep = MathMax(InpGridStep, 200.0); // Standard step
         double sellOffensiveTarget = lastSellPrice - (offensiveStep * pointValue);

         // Check Defensive
         if(bid >= sellDefensiveTarget)
         {
            if(isRedBar && bid < low1) // Reversal Trigger
            {
               if(OpenGridTrade(ORDER_TYPE_SELL, bid, "SELL Recovery (Defensive)", totalSellCount, defensiveStep)) return;
            }
            else if(TimeCurrent() - lastSellWaitLogTime >= 60)
            {
               Print("WAITING - SELL Recovery (Defensive) at target but waiting for Reversal signal... (Bid=", bid, ", Step=", defensiveStep, ")");
               lastSellWaitLogTime = TimeCurrent();
            }
         }
         // Check Offensive
         else if(bid <= sellOffensiveTarget)
         {
            // Minimum Spacing Rule (Sideways Protection)
            double nearestSell = GetNearestPositionPrice(POSITION_TYPE_SELL, bid);
            double minSpacing = MathMax(200.0, InpGridStep * 0.6) * pointValue;
            
            if(nearestSell > 0 && MathAbs(bid - nearestSell) < minSpacing) 
               return; // Skip if too close to any existing SELL

            if(isRedBar && bid < low1) // Trend Signal
            {
               if(OpenGridTrade(ORDER_TYPE_SELL, bid, "SELL Snowball (Offensive)", totalSellCount, offensiveStep)) return;
            }
         }
      }
   }
}

//+------------------------------------------------------------------+
//| Helper to open grid trades and print logs                        |
//+------------------------------------------------------------------+
bool OpenGridTrade(ENUM_ORDER_TYPE type, double price, string logMsg, int layers, double step)
{
   ENUM_POSITION_TYPE posType = (type == ORDER_TYPE_BUY) ? POSITION_TYPE_BUY : POSITION_TYPE_SELL;
   double lotSize = CalculateLotSize(posType);
   if(lotSize <= 0) return false;
   
   if(!IsLotRatioSafe(posType, lotSize))
   {
      static datetime lastRatioLog = 0;
      if(TimeCurrent() - lastRatioLog > 300) {
         Print("⚠ [Risk Manager] Grid Trade skipped: Max Lot Ratio (2x) reached.");
         lastRatioLog = TimeCurrent();
      }
      return false;
   }

   IsProcessingTrade = true;
   lastProcessingTime = TimeCurrent();
   
   bool result = TradeWithRetry(type, lotSize, price, 0, 0, "_Grid");
   
   IsProcessingTrade = false;
   
   if(result)
   {
      Print(logMsg, ": Layers=", layers, " | Step=", step, " | Price=", price);
      return true;
   }
   return false;
}

//+------------------------------------------------------------------+
//| Trade with Retry Mechanism                                       |
//| Retries on Market Closed or Error 4756                         |
//+------------------------------------------------------------------+
bool TradeWithRetry(ENUM_ORDER_TYPE orderType, double lotSize, double price, double sl, double tp, string suffix = "")
{
   bool result = false;
   int retries = 0;
   string comment = InpTradeComment + suffix;
   
   while(retries < InpMaxRetries && !result)
   {
      if(orderType == ORDER_TYPE_BUY)
         result = trade.Buy(lotSize, _Symbol, price, sl, tp, comment);
      else
         result = trade.Sell(lotSize, _Symbol, price, sl, tp, comment);
      
      uint retcode = trade.ResultRetcode();
      
      // Success codes
      if(result && (retcode == TRADE_RETCODE_DONE || retcode == TRADE_RETCODE_PLACED))
      {
         return true;
      }
      
      // Pending/partial - wait and check
      if(retcode == TRADE_RETCODE_PLACED || retcode == TRADE_RETCODE_DONE_PARTIAL)
      {
         Sleep(100);
         retcode = trade.ResultRetcode();
         if(retcode == TRADE_RETCODE_DONE)
         {
            return true;
         }
      }
      
      // Failure - check if we should retry
      int errorCode = GetLastError();
      
      if(errorCode == 4756 || errorCode == 10018 || retcode == 10018 || retcode == 4756)
      {
         retries++;
         if(retries < InpMaxRetries)
         {
            Print("Trade failed (Error: ", errorCode, ", Retcode: ", retcode, "). Retrying... (", retries, "/", InpMaxRetries, ")");
            Sleep(InpRetryDelayMs);
         }
      }
      else
      {
         // Other error - don't retry
         Print("✗ Trade FAILED: Error Code=", errorCode, " | Retcode=", retcode);
         return false;
      }
   }
   
   if(!result)
   {
      Print("✗ Trade FAILED after ", retries, " retries");
   }
   
   return result;
}

//+------------------------------------------------------------------+
//| Calculate Lot Size based on Account Balance                      |
//| Formula: Lot = (AccountBalance() / 10000.0) * 0.1               |
//| Example: $1,000 = 0.01 / $5,000 = 0.05 / $10,000 = 0.10         |
//+------------------------------------------------------------------+
double CalculateLotSize(ENUM_POSITION_TYPE type = -1)
{
   double marginLevel = AccountInfoDouble(ACCOUNT_MARGIN_LEVEL);
   
   // Hard Stop: No new trades if Margin is below Alert Level
   if(marginLevel > 0 && marginLevel < InpMarginAlertLevel)
   {
      return 0; // Return 0 to signal no trade allowed
   }

   // New Dynamic Lot Calculation based on Balance
   // Formula: Lot = (AccountBalance() / 10000.0) * 0.1
   // Example: $1,000 = 0.01 / $5,000 = 0.05 / $10,000 = 0.10
   double balance = AccountInfoDouble(ACCOUNT_BALANCE);
   double lotSize = (balance / 10000.0) * 0.1;
   
   double minLot = SymbolInfoDouble(_Symbol, SYMBOL_VOLUME_MIN);
   double maxLot = SymbolInfoDouble(_Symbol, SYMBOL_VOLUME_MAX);
   double lotStep = SymbolInfoDouble(_Symbol, SYMBOL_VOLUME_STEP);
   
   // Round down to lot step
   lotSize = MathFloor(lotSize / lotStep) * lotStep;
   
   // Apply min/max constraints
   if(lotSize < minLot) lotSize = minLot;
   if(lotSize > maxLot) lotSize = maxLot;
   
   // Debug: Print calculation (throttled to once per minute)
   static datetime lastLotDebug = 0;
   if(TimeCurrent() - lastLotDebug >= 60) {
      Print("[Lot Calc] Balance: $", balance, " | Formula: (", balance, " / 10000) * 0.1 = ", (balance / 10000.0) * 0.1, " | After Step: ", lotSize, " | Min: ", minLot, " | Step: ", lotStep);
      lastLotDebug = TimeCurrent();
   }
   
   return NormalizeDouble(lotSize, 2);
}

//+------------------------------------------------------------------+
//| Check if adding this lot keeps the portfolio within ratio limit  |
//+------------------------------------------------------------------+
bool IsLotRatioSafe(ENUM_POSITION_TYPE type, double newLot)
{
   double buyLots = GetTotalLots(POSITION_TYPE_BUY);
   double sellLots = GetTotalLots(POSITION_TYPE_SELL);
   
   double sideLots = (type == POSITION_TYPE_BUY) ? buyLots : sellLots;
   double oppLots = (type == POSITION_TYPE_BUY) ? sellLots : buyLots;
   
   // If opposite side has lots, check the 2x ratio limit
   if(oppLots > 0)
   {
      if((sideLots + newLot) > oppLots * InpMaxLotRatio) return false;
   }
   // If opposite side is empty, we allow the trade but maybe we could limit absolute size?
   // For now, we follow the "2x opposite" rule which implies opposite must exist.
   
   return true;
}

//+------------------------------------------------------------------+
//| Get human-readable error description                             |
//+------------------------------------------------------------------+
string ErrorDescription(int errorCode)
{
   switch(errorCode)
   {
      case TRADE_RETCODE_DONE: return "Done";
      case TRADE_RETCODE_PLACED: return "Placed";
      case TRADE_RETCODE_NO_MONEY: return "No money";
      case TRADE_RETCODE_MARKET_CLOSED: return "Market closed";
      case TRADE_RETCODE_INVALID_STOPS: return "Invalid stops";
      case TRADE_RETCODE_INVALID_VOLUME: return "Invalid volume";
      case TRADE_RETCODE_INVALID_PRICE: return "Invalid price";
      case TRADE_RETCODE_REJECT: return "Rejected";
      case 4756: return "Trade send failed (4756)";
      default: return "Unknown error (" + IntegerToString(errorCode) + ")";
   }
}
