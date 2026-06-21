# 🏆 Gacha Funds Bot — 1st Place SYNCS 2024 Bot Battle
 
> An AI bot built to play the board game RISK, developed for SYNCYS 2024 Bot Battle competition.
 
---
 
## Overview
 
Gacha Funds Bot is a strategy-driven RISK-playing bot that maximises troop gain while minimising troop loss across all phases of the game. Its decision-making is built around two core game mechanics:
 
- **Continent bonuses** — the primary focus in the early game
- **Territory cards** — the primary focus in the late game
Central to almost every strategy is the concept of **clusters**: sub-graphs of connected territories used to evaluate threats, targets, and attack paths.
 
---
 
## Strategy
 
### Setup Phase
 
- Targets an **empty continent** from the start to secure a bonus as early as possible
- Prioritises claiming **border territories** within the continent (adjacency to other continents) for both defence and future expansion
- If another player moves into the same continent on turn 2, the bot **jumps to a different empty continent** to avoid early conflict
- During the initial fortification phase, troops are distributed equally across:
  - All **border chokepoint territories** in the main cluster (to deter attacks and position for expansion)
  - A single **attacker territory** to finish claiming the starting continent if needed
### Early Game (≤ 6 card sets redeemed)
 
Continent bonuses take priority. Each turn:
 
1. Clusters of unowned territories in nearby continents are identified
2. A **difficulty score** is calculated for each cluster using `T + 2X + 3`, where:
   - `T` = total troops in the cluster
   - `X` = number of territories with more than 1 troop
3. Troops in unowned territories bordering the target are also factored in, to account for post-capture defence
4. If deployable troops meet or exceed the difficulty score → **full continent takeover attempt**
5. Otherwise → **single forced attack** to earn a territory card at turn end, without overcommitting troops
### Late Game (> 6 card sets redeemed)
 
The priority shifts to **eliminating players** and capturing their territory cards. Each turn:
 
1. Clusters are built for each remaining player's territories
2. A Dijkstra-like algorithm finds the lowest-troop path from each cluster to friendly border territories, across three path variants:
   - Least-troop path to any owned border territory
   - Least-troop path to a territory adjacent to the above
   - Least-troop path to the owned territory with the highest troop count
3. A **path score** is calculated by subtracting path troops from the attacking territory's troops
4. The highest-scoring path determines the attacking territory and combined cluster
5. Troops are deployed and the attack is launched if sufficient forces are available
If no player meets the elimination threshold, the bot falls back to its early game continent strategy.
 
---
 
## Implementation Details
 
| Function | Behaviour |
|---|---|
| `handle_claim_territory` | Claims from an empty continent; prioritises border territories, then interior, then adjacent |
| `handle_place_initial_troops` | Distributes troops equally across chokepoint borders and the attacker territory |
| `handle_redeem_cards` | Only redeems when forced (up to 12 card sets redeemed); uses the default redemption logic from `complex.py` |
| `handle_distribute_troops` | Deploys troops to maximise chance of eliminating a target player; falls back to lowest-difficulty continent cluster |
| `handle_attack` | Recalculates target clusters after each capture; attacks non-cut-vertices first to approximate a Hamiltonian path through the cluster |
| `handle_troops_after_attack` | Moves maximum troops by default; moves minimum if it's a forced attack or the territory is non-border; reserves troops for other queued targets |
| `handle_defend` | Always defends with the maximum number of dice |
| `handle_fortify` | Moves troops from the highest-troop non-border territory toward the nearest border territory |
 
---
 
## Key Concepts
 
**Clusters:** Sub-graphs of connected territories used as the primary unit for evaluating attack and defence decisions throughout all game phases.
 
**Difficulty Score:** A heuristic formula `T + 2X + 3` that estimates the troop cost to conquer a cluster. Drives both deployment decisions and target selection.
 
**Cut-Vertex Avoidance:** During attacks, the bot avoids targeting cut-vertices (territories whose removal would split a cluster) until necessary, to maintain a clean sweep path through enemy territory.
 
**SelfState:** An internal state object that persists target cluster data between the distribute and attack phases within a turn, ensuring troops allocated for specific targets aren't inadvertently moved away.
 
---
 
## Tech Stack
 
- **Language:** Python
- **Base:** Adapted from `complex.py` sample bot
- **Algorithm highlights:** Dijkstra-like pathfinding, graph cluster analysis, cut-vertex detection
---
 
## Competition Result
 
🥇 **1st Place** — SYNCS 2024 Bot Battle
