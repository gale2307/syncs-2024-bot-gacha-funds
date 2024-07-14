from collections import defaultdict, deque
import random
import heapq
from typing import Optional, Tuple, Union, cast
from risk_helper.game import Game
from risk_shared.models.card_model import CardModel
from risk_shared.queries.query_attack import QueryAttack
from risk_shared.queries.query_claim_territory import QueryClaimTerritory
from risk_shared.queries.query_defend import QueryDefend
from risk_shared.queries.query_distribute_troops import QueryDistributeTroops
from risk_shared.queries.query_fortify import QueryFortify
from risk_shared.queries.query_place_initial_troop import QueryPlaceInitialTroop
from risk_shared.queries.query_redeem_cards import QueryRedeemCards
from risk_shared.queries.query_troops_after_attack import QueryTroopsAfterAttack
from risk_shared.queries.query_type import QueryType
from risk_shared.records.moves.move_attack import MoveAttack
from risk_shared.records.moves.move_attack_pass import MoveAttackPass
from risk_shared.records.moves.move_claim_territory import MoveClaimTerritory
from risk_shared.records.moves.move_defend import MoveDefend
from risk_shared.records.moves.move_distribute_troops import MoveDistributeTroops
from risk_shared.records.moves.move_fortify import MoveFortify
from risk_shared.records.moves.move_fortify_pass import MoveFortifyPass
from risk_shared.records.moves.move_place_initial_troop import MovePlaceInitialTroop
from risk_shared.records.moves.move_redeem_cards import MoveRedeemCards
from risk_shared.records.moves.move_troops_after_attack import MoveTroopsAfterAttack
from risk_shared.records.record_attack import RecordAttack
from risk_shared.records.types.move_type import MoveType
from time import time


MIN_CHOKE = 4
MIN_ATK = 5
MIN_ATK_SINGLE = 3
MIN_ATK_TROOP_DIFF = 2
MAX_PLAYER_CONTINENT_START = 2
MAX_FORCED_ATK = 2 # Maximum num of troops in enemy territory for forced attack in early game
INIT_MIN_TROOPS = 4
LATE_MIN_TROOPS = 1
DEFENSE_MULTIPLIER = 0.5
TERRITORY_SCORE = 2
ELIM_MOD = 3
#ELIM_MOD_WORST = 4
NOT_FOUND = -1
#BONUS_TROOPS = 4 # Num. of surplus troops given to eliminating players
INF_INT = 99999
NEG_INF_INT = -99999

CL_TYPE_NONE = -1
CL_TYPE_PLAYER = 0
CL_TYPE_CONTINENT = 1
CL_TYPE_DISRUPT = 2
CL_TYPE_FORCED = 3
CL_TYPE_INIT_MY_CONT = 4
CL_TYPE_INIT_OTHER_CONT = 5

#WEAK_PLAYER_MAX = 500
MID_GAME = 0
CARDS_REDEEMED_LATE_GAME = 5


# We will store our enemy in the bot state.
class BotState():
    def __init__(self):
        self.enemy: Optional[int] = None

class Enemy:
    def __init__(self, player_id, clusters):
        self.player_id: int = player_id
        self.clusters: list[list] = clusters

class TargetCluster():
    def __init__(self, id: int, cluster: list[int], ori_cluster: list[int], attacker: int, score: int, recommended_troops: int, type: int):
        self.id: int = id
        self.cluster: list[int] = cluster
        self.ori_cluster: list[int] = ori_cluster
        self.attacker: int = attacker
        self.difficulty_score: int = score
        self.recommended_troops: int = recommended_troops
        #self.wc_remmmended_troops: int = 0
        self.commit: bool = False
        self.type: int = type # 0: player, 1: continent
        self.continent: int = NOT_FOUND

class SelfState():
    def __init__(self):
        self.cont_first_terr = [0, 9, 16, 28, 32, 38, 42]
        self.cont_terr_count = [9, 7, 12, 4, 6, 4]
        self.cont_count = 6
        self.cont_dict: dict[int, list[int]] = dict()
        self.in_choke_points: dict[int, list[int]] = {0: [0, 2, 4], 1: [10, 14, 13, 15], 2: [21, 24, 26, 16, 22], 3: [29, 30], 4: [33, 34, 36], 5: [40]}
        self.out_choke_points: dict[int, list[int]] = {0: [10, 21, 30], 1: [4, 16, 22, 26, 34, 36], 2: [0, 14, 13, 33, 34, 40], 3: [2, 36], 4: [13, 15, 22, 29], 5: [24]}
        self.prio_score: list[int] = [3, 5, 6, 2, 4, 1]

        self.base_prio: list[int] = [3, 5, 0, 4, 1, 2] # Continent priority (1st index highest prio)
        self.cur_prio: list[int] = [] # Current priority attack targets (continents)
        self.cur_owned: list[int] = [] # Currently owned continents
        self.cont_adj: dict[int, list[int]] =  {0: [3, 1, 2], 1: [0, 4, 2], 2: [5, 4, 1], 3: [4, 0], 4: [3, 1, 2], 5: [2]}

        self.weakest_players: list[int] = []
        self.initial_clusters: deque[TargetCluster] = deque()
        self.prio_clusters: deque[TargetCluster] = deque()
        self.cur_cluster: TargetCluster = TargetCluster(-1, [], [], -1, -1, -1, CL_TYPE_NONE)

        #self.cluster_cache: dict[frozenset, TargetCluster] = {}

        self.flag_atk = False #flags if we have attacked this turn or not
        self.flag_forced_atk = False
        self.flag_done_forced_capture = False
        self.flag_cluster_reset = True
        self.flag_cluster_atk = False

        #self.cur_target_continent = -1 #TODO
        self.banned_init_territories: set[int] = set()

        #init territories in each continent
        for i in range(6):
            self.cont_dict[i] = list(range(self.cont_first_terr[i], self.cont_first_terr[i+1]))

    def get_territory_list(self, cont: int):
        return self.cont_dict[cont]
    
    def change_base_prio(self, cont: int):
        new_prio = []
        new_prio.append(cont)
        new_prio = new_prio + self.cont_adj[cont]
        self.base_prio = new_prio

    #def update_weakest_players(self, game: Game):
    #    eliminate_player_difficulty_score = {}
    #    weakest_players = []
    #    for player in game.state.players.values():
    #       if player.player_id == game.state.me.player_id or not player.alive:
    #            continue # Ignore if player is us or knocked out
    #        weakest_players.append(player.player_id)
    #        eliminate_player_difficulty_score[player.player_id] = get_eliminate_player_difficulty_score(game, player.player_id)
    #    self.weakest_players = sorted(weakest_players, key=lambda x: eliminate_player_difficulty_score[x])

    def change_cur_prio(self, game: Game):
        my_cont = get_my_continents(game)
        owned_cont = []
        for cont in my_cont:
            if get_continent_percent_owned(game, cont) >= 1.0:
                owned_cont.append(cont)
        self.cur_owned = owned_cont

        self.cur_prio = list(self.base_prio)
        adj_cont = []

        if len(owned_cont) != 0:
            for cont in owned_cont:
                for x in self.cont_adj[cont]:
                    adj_cont.append(x)
            adj_cont = list(set(adj_cont) - set(owned_cont))
            adj_cont = sorted(adj_cont, key=lambda x: self.prio_score[x])
            self.cur_prio = adj_cont
            # Append remaining countries
            for x in self.base_prio:
                if x not in self.cur_prio and x not in owned_cont:
                    self.cur_prio.append(x)
        else:
            #TODO make this work better, consider troop count

            # If no owned continent, prioritize taking over a continent
            cont_dict = game.state.map.get_continents()
            cont_keys = list(cont_dict.keys())
            top_prio = sorted(cont_keys, key=lambda x: get_continent_percent_owned(game, x), reverse=True)[0]
            print('top_prio: ', top_prio, flush=True)
            adj_cont = self.cont_adj[top_prio]
            adj_cont = sorted(adj_cont, key=lambda x: self.prio_score[x])
            self.cur_prio = [top_prio] + adj_cont
            print('adj_cont: ', adj_cont, flush=True)
            print('cur_prio: ', self.cur_prio, flush=True)

    def get_prio_and_owned_continents(self) -> list[int]:
        return self.cur_owned + self.cur_prio
    
    def reset_cluster(self):
        self.prio_clusters = deque()
        self.cur_cluster = TargetCluster(-1, [], [], -1, -1, -1, CL_TYPE_NONE)
        self.flag_cluster_reset = True

def main():
    
    # Get the game object, which will connect you to the engine and
    # track the state of the game.
    game = Game()
    bot_state = BotState()
    self_state = SelfState()
   
    # Respond to the engine's queries with your moves.
    while True:

        # Get the engine's query (this will block until you receive a query).
        query = game.get_next_query()

        # Based on the type of query, respond with the correct move.
        def choose_move(query: QueryType) -> MoveType:
            match query:
                case QueryClaimTerritory() as q:
                    return handle_claim_territory(game, self_state, bot_state, q)

                case QueryPlaceInitialTroop() as q:
                    return handle_place_initial_troop(game, self_state, bot_state, q)

                case QueryRedeemCards() as q:
                    return handle_redeem_cards(game, self_state, bot_state, q)

                case QueryDistributeTroops() as q:
                    return handle_distribute_troops(game, self_state, bot_state, q)

                case QueryAttack() as q:
                    return handle_attack(game, self_state, bot_state, q)

                case QueryTroopsAfterAttack() as q:
                    return handle_troops_after_attack(game, self_state, bot_state, q)

                case QueryDefend() as q:
                    return handle_defend(game, self_state, bot_state, q)

                case QueryFortify() as q:
                    return handle_fortify(game, self_state, bot_state, q)
        
        # Send the move to the engine.
        game.send_move(choose_move(query))
                

def handle_claim_territory(game: Game, self_state: SelfState, bot_state: BotState, query: QueryClaimTerritory) -> MoveClaimTerritory:
    """At the start of the game, you can claim a single unclaimed territory every turn 
    until all the territories have been claimed by players."""

    #TODO make continent graph to change priorities reactively
    unclaimed_territories = game.state.get_territories_owned_by(None)
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    selected_territory = unclaimed_territories[0]
    #print("unclaimed[0]: " + str(unclaimed_territories[0]), flush=True)
    conts = get_my_continents(game)
    #banned_conts = set()
    #banned_territories = set()
    flag_retry = False

    # if len(conts) == 1 and 
    if len(my_territories) == 1 and len(get_players_in_continent(game, conts[0])) >= MAX_PLAYER_CONTINENT_START:
        #banned_conts.add(conts[0])
        self_state.banned_init_territories = set(game.state.map.get_continents()[conts[0]])
        flag_retry = True

    if len(my_territories) <= 0 or flag_retry:
        selected_territory = NOT_FOUND
        for i in range(6):
            is_empty = True
            cont = self_state.base_prio[i]
            cont_terr = game.state.map.get_continents()[cont]
            cont_available = list(set(unclaimed_territories) & set(cont_terr))
            if len(cont_available) != len(cont_terr):
                is_empty = False

            if is_empty:
                candidates = game.state.map.get_continents()[cont]
                selected_territory = get_highest_priority_starting_territory(game, self_state, candidates, set([cont]))[0]
                break
        
        if selected_territory == NOT_FOUND:
            least_players_cont = min(game.state.map.get_continents().keys(), key=lambda x: get_players_in_continent(game, x))
            candidates = intersect_territories(game.state.map.get_continents()[cont], unclaimed_territories)
            selected_territory = get_highest_priority_starting_territory(game, self_state, candidates, set([least_players_cont]))[0]
        
        return game.move_claim_territory(query, selected_territory)
        

    #first, find empty continent
    #then, claim land in that continent
    #if not available, get adjacent land
    #adjacent_territories = game.state.get_all_adjacent_territories(my_territories)
    score = NOT_FOUND
    unbanned_unclaimed_territories = list(set(unclaimed_territories)-self_state.banned_init_territories)
    if len(unbanned_unclaimed_territories) > 0:
        selected_territory, score = get_highest_priority_starting_territory(game, self_state, list(set(unclaimed_territories)-self_state.banned_init_territories), set(conts))
    if score == NOT_FOUND:
        my_clusters = get_player_clusters(game, game.state.me.player_id)
        my_main_cluster = sorted(my_clusters, key=lambda x: get_troops_in_cluster(game, x), reverse=True)[0]
        closest_node = find_closest_node_from_cluster_to_set(game, my_main_cluster, set(unclaimed_territories), set())
        selected_territory = closest_node
    return game.move_claim_territory(query, selected_territory)

def handle_place_initial_troop(game: Game, self_state: SelfState, bot_state: BotState, query: QueryPlaceInitialTroop) -> MovePlaceInitialTroop:
    """After all the territories have been claimed, you can place a single troop on one
    of your territories each turn until each player runs out of troops."""

    # Avoid troop < INIT_MIN_TROOPS territories early in main cluster
    # TODO: This does not consider that we can have more than 1 cluster in the same continent
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    border_territories = game.state.get_all_border_territories(my_territories)
    #my_clusters = get_player_clusters(game, game.state.me.player_id)
    #my_main_cluster = sorted(my_clusters, key=lambda x: get_troops_in_cluster(game, x), reverse=True)[0]
    #for territory in my_main_cluster:
    #    if game.state.territories[territory].troops < INIT_MIN_TROOPS:
    #        return game.move_place_initial_troop(query, territory)

    #focus troops on one continent to take early control
    cont_dict = game.state.map.get_continents()
    cont_keys = list(cont_dict.keys())
    
    priority_continent = sorted(cont_keys, key=lambda x: get_continent_percent_owned(game, x), reverse=True)[0]
    self_state.change_base_prio(priority_continent)#TODO should only run once

    # Get all border(continent territory U owned_out_choke)
    #border_territories = game.state.get_all_border_territories(my_territories)
    out_choke_territories = self_state.out_choke_points[priority_continent]
    owned_out_choke = list(set(out_choke_territories) & set(my_territories)) #important

    owned_in_choke = intersect_territories(self_state.in_choke_points[priority_continent], my_territories)
    border_in_choke = intersect_territories(self_state.in_choke_points[priority_continent], border_territories)

    priority_territories = border_in_choke
    non_border_in_choke = list(set(owned_in_choke) - set(border_in_choke))
    for t in non_border_in_choke:
        adjacent_out_choke = intersect_territories(game.state.map.get_adjacent_to(t), owned_out_choke)
        if len(adjacent_out_choke) <= 1:
            priority_territories = list(set(priority_territories).union(set(adjacent_out_choke)))

    #continent_all_territory = game.state.map.get_continents()[priority_continent]
    #priority_territories = game.state.get_all_border_territories(continent_all_territory + owned_out_choke)
    #priority_territories = intersect_territories(priority_territories, my_territories)

    for territory in priority_territories:
        if game.state.territories[territory].troops < INIT_MIN_TROOPS:
            return game.move_place_initial_troop(query, territory)

    # If we don't own the continent, attempt to assign an attacker
    if len(self_state.initial_clusters) <=0:
        if get_continent_percent_owned(game, priority_continent) < 1.0:
            unowned_in_continent = get_unowned_in_continent(game, priority_continent)
            clusters = get_clusters(game, unowned_in_continent)
            for cluster in clusters:
                candidates = get_cluster_adjacent_friendly(game, cluster)
                non_border_candidates = list(set(candidates) - set(priority_territories))
                if len(non_border_candidates) > 0:
                    candidates = non_border_candidates
                target_cluster = TargetCluster(0, cluster, cluster, candidates[0], 0, 0, CL_TYPE_CONTINENT)
                self_state.initial_clusters.append(target_cluster)
        else:
            adj_cont = self_state.cont_adj[priority_continent]
            next_target_continent = min(adj_cont, key=lambda x: get_cluster_difficulty_score(game, get_unowned_in_continent(game, x)))
            target_territories = get_unowned_in_continent(game, next_target_continent)
            attacker = max(get_cluster_adjacent_friendly(game, target_territories), key=lambda x: game.state.territories[x].troops)
            target_cluster = TargetCluster(0, target_territories, target_territories, attacker, 0, 0, CL_TYPE_CONTINENT)
            self_state.initial_clusters.append(target_cluster)
    
    tmp = self_state.initial_clusters.popleft()
    self_state.initial_clusters.append(tmp)

    highest_diff_score = 0
    highest_diff_cluster_attacker = NOT_FOUND
    for target in self_state.initial_clusters:
        diff_score = get_cluster_difficulty_score(game, target.cluster)
        if diff_score > game.state.territories[target.attacker].troops:
            return game.move_place_initial_troop(query, target.attacker)
        if diff_score > highest_diff_score:
            highest_diff_score = diff_score
            highest_diff_cluster_attacker = target.attacker
    
    return game.move_place_initial_troop(query, highest_diff_cluster_attacker)


    """
    cur_target_cluster = self_state.initial_clusters.popleft()
    self_state.initial_clusters.append(cur_target_cluster)

    

    if get_continent_percent_owned(game, priority_continent) < 1.0:
        owned_in_continent = get_owned_in_continent(game, priority_continent)
        attacker_candidates = list(set(owned_in_continent)-set(priority_territories))
        if len(attacker_candidates) > 0:
            attacker = max(attacker_candidates, key=lambda x: game.state.territories[x].troops + len(set(my_territories) & set(game.state.map.get_adjacent_to(x))))
            priority_territories.append(attacker)

    #priority_territories = get_owned_in_continent(game, self_state, priority_continent)
    #priority_territories = list(set(priority_territories) & set(border_territories)) #in-continent & borders
    #priority_territories = list(set(priority_territories) | set(owned_out_choke)) # + important choke points

    # We will place a troop in a priority territory with the least troops currently
    # on it. This should give us close to an equal distribution.
    priority_territory_models = [game.state.territories[x] for x in priority_territories]
    min_troops_territory = min(priority_territory_models, key=lambda x: x.troops)

    return game.move_place_initial_troop(query, min_troops_territory.territory_id)
    """

def handle_redeem_cards(game: Game, self_state: SelfState, bot_state: BotState, query: QueryRedeemCards) -> MoveRedeemCards:
    """After the claiming and placing initial troops phases are over, you can redeem any
    cards you have at the start of each turn, or after killing another player."""
    #TODO

    # We will always redeem the minimum number of card sets we can until the 12th card set has been redeemed.
    # This is just an arbitrary choice to try and save our cards for the late game.

    # We always have to redeem enough cards to reduce our card count below five.
    card_sets: list[Tuple[CardModel, CardModel, CardModel]] = []
    cards_remaining = game.state.me.cards.copy()

    while len(cards_remaining) >= 5:
        card_set = game.state.get_card_set(cards_remaining)
        # According to the pigeonhole principle, we should always be able to make a set
        # of cards if we have at least 5 cards.
        assert card_set != None
        card_sets.append(card_set)
        cards_remaining = [card for card in cards_remaining if card not in card_set]

    # Remember we can't redeem any more than the required number of card sets if 
    # we have just eliminated a player.
    if game.state.card_sets_redeemed > CARDS_REDEEMED_LATE_GAME and query.cause == "turn_started":
        card_set = game.state.get_card_set(cards_remaining)
        while card_set != None:
            card_sets.append(card_set)
            cards_remaining = [card for card in cards_remaining if card not in card_set]
            card_set = game.state.get_card_set(cards_remaining)

    return game.move_redeem_cards(query, [(x[0].card_id, x[1].card_id, x[2].card_id) for x in card_sets])


def handle_distribute_troops(game: Game, self_state: SelfState, bot_state: BotState, query: QueryDistributeTroops) -> MoveDistributeTroops:
    """After you redeem cards (you may have chosen to not redeem any), you need to distribute
    all the troops you have available across your territories. This can happen at the start of
    your turn or after killing another player.
    """
    self_state.change_cur_prio(game)
    #cur_prio = self_state.cur_prio[0]
    self_state.reset_cluster()
    #self_state.update_weakest_players(game)

    # We will distribute troops across our border territories.
    total_troops = game.state.me.troops_remaining
    distributions = defaultdict(lambda: 0)
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    border_territories = game.state.get_all_border_territories(my_territories)

    my_clusters = get_player_clusters(game, game.state.me.player_id)
    my_main_cluster = sorted(my_clusters, key=lambda x: get_troops_in_cluster(game, x), reverse=True)[0]
    main_border_territories = game.state.get_all_border_territories(my_main_cluster)

    # We need to remember we have to place our matching territory bonus
    # if we have one.
    if len(game.state.me.must_place_territory_bonus) != 0:
        assert total_troops >= 2
        distributions[game.state.me.must_place_territory_bonus[0]] += 2
        total_troops -= 2

    # Give 1 troop each time to key defending territories early on
    if len(game.state.recording) < MID_GAME:
        for territory in main_border_territories:
            if total_troops <= 0:
                break
            territory_cont = get_territory_continent(territory)

            if territory_cont in self_state.get_prio_and_owned_continents() and game.state.territories[territory].troops <= MIN_CHOKE:
                distributions[territory] += 1
                total_troops -= 1

    # Generate clusters to attack weakest players
    player_dstrb: list[TargetCluster] = []
    continent_dstrb: list[TargetCluster] = []
    disrupt_dstrb: list[TargetCluster] = []
    forced_dstrb: list[TargetCluster] = []

    player_total_difficulty = 0
    player_assigned_troops = 0
    continent_total_difficulty = 0
    continent_assigned_troops = 0
    target_continents = set()
    continent_required_troops: dict[int, int] = defaultdict(lambda: 0)
    continent_cluster_count: dict[int, int] = defaultdict(lambda: 0)

    print('dstrb', flush=True)
    for target_cluster in generate_priority_clusters(game, self_state, total_troops):

        if target_cluster.type == CL_TYPE_PLAYER:
            print('pl_cluster: ', target_cluster.cluster, flush=True)
            player_dstrb.append(target_cluster)
            player_total_difficulty += target_cluster.difficulty_score
            player_assigned_troops += target_cluster.recommended_troops
            
        elif target_cluster.type == CL_TYPE_CONTINENT:
            print('cl_cluster: ', target_cluster.cluster, ' | continent: ', target_cluster.continent, flush=True)
            target_continents.add(target_cluster.continent)
            continent_total_difficulty += target_cluster.difficulty_score
            continent_required_troops[target_cluster.continent] += target_cluster.recommended_troops
            continent_cluster_count[target_cluster.continent] += 1
            continent_dstrb.append(target_cluster)

        elif target_cluster.type == CL_TYPE_DISRUPT:
            disrupt_dstrb.append(target_cluster)

        elif target_cluster.type == CL_TYPE_FORCED:
            forced_dstrb.append(target_cluster)
    
    # DEFENSIVE PLAY FOR LATE GAME
    if game.state.card_sets_redeemed > CARDS_REDEEMED_LATE_GAME:
        if len(player_dstrb) <= 0:
            defensive_troops = int(total_troops*DEFENSE_MULTIPLIER)
            for territory in my_territories:
                if defensive_troops <= 0:
                    break
                if game.state.territories[territory].troops < LATE_MIN_TROOPS:
                    distributions[territory] += 1
                    defensive_troops -= 1
                    total_troops -= 1

    continent_assigned_troops = total_troops-player_assigned_troops
    print('ct_asg_trps: ', continent_assigned_troops, flush=True)

    if len(player_dstrb) > 0 and continent_assigned_troops > 0:
        for dstrb in player_dstrb:
            bonus_troops = (continent_assigned_troops*dstrb.difficulty_score)//player_total_difficulty
            dstrb.recommended_troops += bonus_troops
            continent_assigned_troops -= bonus_troops
            if continent_assigned_troops <= 0:
                break
        player_dstrb[0].recommended_troops += continent_assigned_troops
        continent_assigned_troops -= continent_assigned_troops
    
    for dstrb in player_dstrb:
        self_state.prio_clusters.append(dstrb)
        distributions[dstrb.attacker] += dstrb.recommended_troops
        total_troops -= dstrb.recommended_troops

    if len(continent_dstrb) > 0:
        for dstrb in continent_dstrb:
            if continent_assigned_troops <= 0:
                break
            self_state.prio_clusters.append(dstrb)
            assigned_troops = min(dstrb.recommended_troops, total_troops)
            distributions[dstrb.attacker] += assigned_troops
            continent_assigned_troops -= assigned_troops
            total_troops -= assigned_troops

    if len(disrupt_dstrb) > 0:
        for dstrb in disrupt_dstrb:
            if total_troops <= 0:
                break
            self_state.prio_clusters.append(dstrb)
            assigned_troops = min(dstrb.recommended_troops, total_troops)

            distributions[dstrb.attacker] += assigned_troops
            continent_assigned_troops -= assigned_troops
            total_troops -= assigned_troops
    
    # Distribute remaining troops among target continents
    if len(continent_dstrb) > 0:
        remaining_troops = total_troops
        highest_diff_score_attacker = NOT_FOUND
        highest_diff_score = 0
        for dstrb in continent_dstrb:
            bonus_troops = (remaining_troops*dstrb.difficulty_score)//continent_total_difficulty
            distributions[dstrb.attacker] += bonus_troops
            total_troops -= bonus_troops
            if dstrb.difficulty_score > highest_diff_score:
                highest_diff_score = dstrb.difficulty_score
                highest_diff_score_attacker = dstrb.attacker
        
        distributions[highest_diff_score_attacker] += total_troops
        total_troops  = 0

    """
    #tmp
    if len(continent_dstrb) > 0:
        priority_target_cont = sorted(list(target_continents), key=lambda x: continent_required_troops[x])[0]
        remainder = continent_assigned_troops%continent_cluster_count[priority_target_cont]
        #continent_assigned_troops -= remainder
        print('prio_t_cont: ', priority_target_cont, flush=True)
        print('rmndr: ', remainder, flush=True)

        for dstrb in continent_dstrb:
            if continent_assigned_troops <= 0:
                break
            if dstrb.continent == priority_target_cont:
                troops_assigned = (continent_assigned_troops//continent_cluster_count[priority_target_cont]) + remainder
                remainder = 0
                self_state.prio_clusters.append(dstrb)
                distributions[dstrb.attacker] += troops_assigned
                #continent_assigned_troops -= troops_assigned
                total_troops -= troops_assigned
    """

    #if len(disrupt_dstrb) > 0:
    #    for dstrb in disrupt_dstrb:
    #        distributions[dstrb.attacker] += dstrb.recommended_troops
    #        total_troops -= dstrb.recommended_troops
    
    # Expect only 1 forced
    for dstrb in forced_dstrb:
        self_state.prio_clusters.append(dstrb)
        distributions[dstrb.attacker] += total_troops
        total_troops -= total_troops
        break

    self_state.flag_cluster_reset = False
    
    return game.move_distribute_troops(query, distributions)


def handle_attack(game: Game, self_state: SelfState, bot_state: BotState, query: QueryAttack) -> Union[MoveAttack, MoveAttackPass]:
    """After the troop phase of your turn, you may attack any number of times until you decide to
    stop attacking (by passing). After a successful attack, you may move troops into the conquered
    territory. If you eliminated a player you will get a move to redeem cards and then distribute troops."""
    start_time = time()

    self_state.change_cur_prio(game)
    #cur_prio = self_state.cur_prio[0]
    #self_state.update_weakest_players(game)

    if self_state.flag_cluster_reset:
        for target_cluster in generate_priority_clusters(game, self_state, 0):
            self_state.prio_clusters.append(target_cluster)
        self_state.flag_cluster_reset = False

    print("Done gen clusters --- %s seconds ---" % (time() - start_time), flush=True)

    print('\nround = %d', len(game.state.recording), flush=True)
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    #target_territories = game.state.get_all_adjacent_territories(my_territories)
    border_territories = game.state.get_all_border_territories(my_territories)

    def attempt_attack(a, t) -> Optional[MoveAttack]:
        a_troops = game.state.territories[a].troops
        t_troops = game.state.territories[t].troops
        if t_troops <= 1:
            if a_troops >= MIN_ATK_SINGLE:
                self_state.flag_atk = True
                return game.move_attack(query, a, t, min(3, game.state.territories[a].troops - 1))
        else:
            if a_troops >= MIN_ATK and a_troops >= (t_troops + MIN_ATK_TROOP_DIFF):
                self_state.flag_atk = True
                return game.move_attack(query, a, t, min(3, game.state.territories[a].troops - 1))
            
        return None

    print("CURRENT_CLUSTERS", flush=True)
    print("cluster: ", self_state.cur_cluster.cluster, "ori_cluster: ", self_state.cur_cluster.ori_cluster, 
          "\nscore: ", self_state.cur_cluster.difficulty_score, " | rec_troops: ", self_state.cur_cluster.recommended_troops, 
          "\n continent: ", self_state.cur_cluster.continent, " | type: ", self_state.cur_cluster.type, flush=True)
    print("PRIO_CLUSTERS", flush=True)
    for p_cluster in self_state.prio_clusters:
        print("cluster: ", p_cluster.cluster, "ori_cluster: ", p_cluster.ori_cluster,
               "\nscore: ", p_cluster.difficulty_score, " | rec_troops: ", p_cluster.recommended_troops, 
               "\n continent: ", p_cluster.continent, " | type: ", p_cluster.type, flush=True)
    
    while len(self_state.prio_clusters) > 0 or len(self_state.cur_cluster.cluster) > 0:
        #print('prio_clusters: ', self_state.prio_clusters, flush=True)
        if len(self_state.cur_cluster.cluster) <= 0:
            self_state.cur_cluster = self_state.prio_clusters.popleft()

        cluster_attacker = get_cluster_best_attacker(game, self_state.cur_cluster.cluster)
        candidate_targets = get_adjacent_territories_in_cluster(game, cluster_attacker, self_state.cur_cluster.cluster)
        #print('target candidates: ', candidate_targets, flush=True)

        if self_state.cur_cluster.type == CL_TYPE_FORCED and self_state.flag_done_forced_capture:
            self_state.cur_cluster = TargetCluster(-1, [], [], -1, -1,- 1, CL_TYPE_NONE)
            continue

        extra = []
        if (self_state.cur_cluster.type == CL_TYPE_CONTINENT or self_state.cur_cluster.type == CL_TYPE_FORCED) and len(set(self_state.cur_cluster.cluster) - set(self_state.cur_cluster.ori_cluster)) <= 0:
            continent = self_state.cur_cluster.continent # continent we are attacking
            out_choke = self_state.out_choke_points[continent]
            adjacent_to_cluster = game.state.get_all_adjacent_territories(self_state.cur_cluster.cluster)
            candidate_extra = list(set(out_choke) - set(my_territories))
            candidate_extra = intersect_territories(candidate_extra, adjacent_to_cluster)

            for cont in self_state.cur_prio:
                for territory in candidate_extra:
                    if territory in game.state.map.get_continents()[cont]:
                        extra.append(territory)
                        break
                if len(extra) >=1:
                    break

        print('pre-sorted target candidates: ', candidate_targets, flush=True)
        #candidate_targets = sorted(candidate_targets, key=lambda x: is_target_cut_node(game, self_state.cur_cluster.cluster + extra, x))
        candidate_targets = sort_attack_priority(game, self_state.cur_cluster.cluster + extra, candidate_targets)
        for target in candidate_targets:
            move = attempt_attack(cluster_attacker, target)
            if move != None:
                self_state.flag_cluster_atk = True
                print('target candidates: ', candidate_targets, flush=True)
                print('target: ', target, flush=True)
                print('target cluster: ', self_state.cur_cluster.cluster, flush=True)
                print('my territories: ', my_territories, flush=True)
                print("D --- %s seconds ---" % (time() - start_time), flush=True)
                return move
                
        #TODO: resets cur_cluster, can be improved
        self_state.cur_cluster = TargetCluster(-1, [], [], -1, -1,- 1, CL_TYPE_NONE)
 
    # Attack at least once a turn to get card
    #if not self_state.flag_atk:
    #    for border_territory in border_territories:
    #        #print('border: %d', border_territory, flush=True)
    #        if game.state.territories[border_territory].troops >= MIN_ATK: 
    #            candidate_targets = get_adjacent_enemy_territories(game, self_state, border_territory)
    #            for x in candidate_targets:
    #                if game.state.territories[border_territory].troops >= game.state.territories[x].troops + MIN_ATK_TROOP_DIFF:
    #                    self_state.flag_atk = True
    #                    self_state.flag_forced_atk = True
                        #print("B --- %s seconds ---" % (time() - start_time), flush=True)
    #                    return game.move_attack(query, border_territory, x, min(3, game.state.territories[border_territory].troops - 1))

    # In the late game, we will attack anyone adjacent to our strongest territories (hopefully our doomstack).
    #else:
    #    strongest_territories = sorted(my_territories, key=lambda x: game.state.territories[x].troops, reverse=True)
    #    for territory in strongest_territories:
    #        move = attack_weakest(list(set(game.state.map.get_adjacent_to(territory)) - set(my_territories)))
    #        if move != None:
    #            return move

    #print("C --- %s seconds ---" % (time() - start_time), flush=True)
    return game.move_attack_pass(query)


def handle_troops_after_attack(game: Game, self_state: SelfState, bot_state: BotState, query: QueryTroopsAfterAttack) -> MoveTroopsAfterAttack:
    """After conquering a territory in an attack, you must move troops to the new territory."""
    #TODO
    # After attack, if source was border and in-choke, leave MIN_CHOKE troops

    # First we need to get the record that describes the attack, and then the move that specifies
    # which territory was the attacking territory.
    # self_state.flag_atk = True

    record_attack = cast(RecordAttack, game.state.recording[query.record_attack_id])
    move_attack = cast(MoveAttack, game.state.recording[record_attack.move_attack_id])

    booked_troops = 0
    self_state.flag_done_forced_capture = True

    attack_type = self_state.cur_cluster.type # Cluster type of attack done

    if self_state.flag_cluster_atk:
        #print('cur_cluster: ', self_state.cur_cluster.cluster, flush=True)
        #print('defending: ', move_attack.defending_territory, flush=True)
        #print('attacking: ', move_attack.attacking_territory, flush=True)
        #self_state.cur_cluster.cluster.remove(move_attack.defending_territory)
        for cluster in self_state.prio_clusters:
            # Prioritize troop bookings with higher or equal priority
            if cluster.attacker == move_attack.attacking_territory and cluster.type <= attack_type:
                if move_attack.defending_territory not in cluster.cluster:
                    booked_troops += cluster.difficulty_score
                    print('Booked by: ', cluster.cluster, ' | num: ', cluster.difficulty_score, flush=True)
        print('Booked troops total: ', booked_troops, flush=True)
    self_state.reset_cluster()
    self_state.flag_cluster_atk = False

    if attack_type == CL_TYPE_FORCED:
        print('Is forced attack', flush=True)
        return game.move_troops_after_attack(query, move_attack.attacking_troops)
    
    if attack_type == CL_TYPE_DISRUPT:
        return game.move_troops_after_attack(query, move_attack.attacking_troops)

    #if self_state.flag_forced_atk:
    #    self_state.flag_forced_atk = False
    #    print('Is forced attack', flush=True)
    #    return game.move_troops_after_attack(query, move_attack.attacking_troops)

    adjacent_territories = game.state.map.get_adjacent_to(move_attack.defending_territory)
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    border_territories = game.state.get_all_border_territories(my_territories)
    continent = get_territory_continent(move_attack.attacking_territory)
    in_choke = self_state.in_choke_points[continent]

    #for target_cluster in generate_priority_clusters(game, 0):
    #    self_state.prio_clusters.append(target_cluster)

    #if conquered territory is not border, move minimum amount
    if len(set(adjacent_territories) - set(my_territories)) <= 0:
        print('Conquered territory is border', flush=True)
        return game.move_troops_after_attack(query, move_attack.attacking_troops)

    if game.state.card_sets_redeemed > CARDS_REDEEMED_LATE_GAME and attack_type != CL_TYPE_PLAYER:
        moving_troops = max(game.state.territories[move_attack.attacking_territory].troops - LATE_MIN_TROOPS, move_attack.attacking_troops)
        return game.move_troops_after_attack(query, moving_troops)

    #TODO update to consider choke that borders 2 continents
    # Don't do this if late game
    if move_attack.attacking_territory in (set(border_territories) & set(in_choke)) and len(game.state.recording) < MID_GAME:#MID_GAME
        moving_troops = max(game.state.territories[move_attack.attacking_territory].troops - max(MIN_CHOKE, booked_troops), move_attack.attacking_troops)
        print('Attacking territory is choke', flush=True)
        return game.move_troops_after_attack(query, moving_troops)

    # We will always move the maximum number of troops we can.
    return game.move_troops_after_attack(query, max(game.state.territories[move_attack.attacking_territory].troops - max(1, booked_troops), move_attack.attacking_troops))


def handle_defend(game: Game, self_state: SelfState, bot_state: BotState, query: QueryDefend) -> MoveDefend:
    """If you are being attacked by another player, you must choose how many troops to defend with."""

    # We will always defend with the most troops that we can.

    # First we need to get the record that describes the attack we are defending against.
    move_attack = cast(MoveAttack, game.state.recording[query.move_attack_id])
    defending_territory = move_attack.defending_territory
    
    # We can only defend with up to 2 troops, and no more than we have stationed on the defending
    # territory.
    defending_troops = min(game.state.territories[defending_territory].troops, 2)
    return game.move_defend(query, defending_troops)


def handle_fortify(game: Game, self_state: SelfState, bot_state: BotState, query: QueryFortify) -> Union[MoveFortify, MoveFortifyPass]:
    """At the end of your turn, after you have finished attacking, you may move a number of troops between
    any two of your territories (they must be adjacent)."""

    #print("Fortify start")
    self_state.flag_atk = False
    self_state.flag_done_forced_capture = False

    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    border_territories = game.state.get_all_border_territories(my_territories)

    non_border_territories = list(set(my_territories)-set(border_territories))
    if len(non_border_territories) <= 0:
        print("No border territory found")
        return game.move_fortify_pass(query)

    non_border_territories = sorted(non_border_territories, key=lambda x: game.state.territories[x].troops, reverse=True)
    fortify_source = non_border_territories[0]
    shortest_path = find_shortest_path_from_vertex_to_set(game, fortify_source, set(border_territories))
    #print("shortest path: ", shortest_path, flush=True)
    #print("fortify source: ", fortify_source, flush=True)
    if len(shortest_path) > 0 and game.state.territories[fortify_source].troops > 1:
        return game.move_fortify(query, fortify_source, shortest_path[0], game.state.territories[fortify_source].troops - 1)

    return game.move_fortify_pass(query)

def find_shortest_path_from_vertex_to_set(game: Game, source: int, target_set: set[int]) -> list[int]:
    """Used in move_fortify()."""

    # We perform a BFS search from our source vertex, stopping at the first member of the target_set we find.
    queue = deque()
    queue.appendleft(source)

    current = queue.pop()
    parent = {}
    seen = {current: True}

    #print(len(queue), flush=True)
    while True:
        if current in target_set:
            break

        for neighbour in game.state.map.get_adjacent_to(current):
            if neighbour not in seen:
                seen[neighbour] = True
                parent[neighbour] = current
                queue.appendleft(neighbour)

        if len(queue) <= 0:
            break
        current = queue.pop()

    path = []
    while current in parent:
        path.append(current)
        current = parent[current]

    return path[::-1]

def find_closest_node_from_cluster_to_set(game: Game, source_cluster: list[int], target_set: set[int], banned: set[int]) -> int:
    """Used in initial territory claim."""

    # We perform a BFS search from our source vertex, stopping at the first member of the target_set we find.
    queue = deque()
    #queue.appendleft(source)

    #current = queue.pop()
    #parent = {}
    seen: dict[int, bool] = {}

    for x in source_cluster:
        #queue.append(x)
        seen[x] = True

    for x in game.state.get_all_adjacent_territories(source_cluster):
        if x not in banned:
            seen[x] = True
            queue.append(x)
    current = queue.pop()

    #print(len(queue), flush=True)
    while True:
        if current in target_set:
            break

        for neighbour in game.state.map.get_adjacent_to(current):
            if neighbour not in seen and neighbour not in banned:
                seen[neighbour] = True
                #parent[neighbour] = current
                queue.appendleft(neighbour)

        if len(queue) <= 0:
            break
        current = queue.pop()

    return current

def get_territory_weight_wrt_cluster(game: Game, territory: int, cluster: list[int]) -> int:
    if territory in cluster:
        return 0
    
    #TODO: consider troop count in territory
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    if territory in my_territories:
        return 0
    
    troop_count = game.state.territories[territory].troops

    if troop_count == 1:
        return troop_count
    
    return troop_count + 1

# targets = our border territories
# returns path to cluster ([0] is border territory closest to cluster)
def get_best_path_to_cluster(game: Game, cluster: list[int], targets: list[int], banned: set[int]) -> tuple[list[int], int]:
    # Initialize minimum weights and priority queue    
    start = cluster[0]
    min_weights = {node: INF_INT for node in range(0,42)}
    min_weights[start] = get_territory_weight_wrt_cluster(game, start, cluster)
    priority_queue = [(min_weights[start], start)]  # (accumulated weight, node)
    parent = {start: NOT_FOUND}

    #territories_adjacent_to_cluster = game.state.get_all_adjacent_territories(cluster)
    
    while priority_queue:
        current_weight, current_node = heapq.heappop(priority_queue)
        
        # If we reached one of the target nodes, return the accumulated weight
        if current_node in targets:
            path = []
            while current_node != NOT_FOUND:
                path.append(current_node)
                current_node = parent[current_node]
            return (path, current_weight)
        
        # If the popped node has a greater weight than the known minimum weight, skip it
        if current_weight > min_weights[current_node]:
            continue
        
        # Explore adjacent territories
        for adjacent_territory in game.state.map.get_adjacent_to(current_node):
            if adjacent_territory in banned:
                continue
            weight = current_weight + get_territory_weight_wrt_cluster(game, adjacent_territory, targets)
            
            # Only consider this new path if it's better
            if weight < min_weights[adjacent_territory]:
                min_weights[adjacent_territory] = weight
                parent[adjacent_territory] = current_node
                heapq.heappush(priority_queue, (weight, adjacent_territory))
    
    # If none of the targets are reachable, return infinity or an appropriate value
    return [], INF_INT

def get_territory_continent(territory: int) -> int:
    cont_first_terr = [0, 9, 16, 28, 32, 38, 42]
    for i in range(6):
        if territory < cont_first_terr[i+1]:
            return i
        
    #shouldn't get here
    return 99

def get_my_continents(game: Game) -> list[int]:
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    my_continents = set()
    for i in my_territories:
        my_continents.add(get_territory_continent(i))
        
    return list(my_continents)

def get_continent_territory(game: Game, self_state: SelfState) -> list[int]:
    continent_territory = []
    conts = get_my_continents(game)
    for cont in conts:
        #continent_territory = continent_territory + self_state.get_territory_list(cont)
        continent_territory = continent_territory + game.state.map.get_continents()[cont]
        
    return continent_territory

def get_owned_in_continent(game: Game, continent: int) -> list[int]:
    all_t = game.state.map.get_continents()[continent]
    owned_t = game.state.get_territories_owned_by(game.state.me.player_id)
    return list(set(all_t) & set(owned_t))

def get_unowned_in_continent(game: Game, continent: int) -> list[int]:
    all_t = game.state.map.get_continents()[continent]
    owned_t = game.state.get_territories_owned_by(game.state.me.player_id)
    return list(set(all_t) - set(owned_t))

def get_continent_percent_owned(game: Game, continent: int) -> float:
    all_t = game.state.map.get_continents()[continent]
    owned_t = game.state.get_territories_owned_by(game.state.me.player_id)
    owned_in_continent = list(set(all_t) & set(owned_t))
    return float(len(owned_in_continent))/float(len(all_t))

def get_cluster_percent_owned_complex(game: Game, cluster: list[int], deployable_troops: int) -> float:
    # Get ratio of owned troops and territory in cluster
    total_troops = 0.0
    owned_troops = 0.0
    owned_troops += deployable_troops
    for node in cluster:
        if game.state.territories[node].occupier == game.state.me.player_id:
            owned_troops += game.state.territories[node].troops
        total_troops += game.state.territories[node].troops

    return owned_troops/total_troops

def union_continent_territories(game: Game, territories: list[int], continent: int) -> list[int]:
    all_t = game.state.map.get_continents()[continent]
    union_list = list(set(all_t) & set(territories))
    return union_list

def intersect_territories(a: list[int], b:list[int]) -> list[int]:
    return list(set(a) & set(b))

def get_candidate_attacker(game: Game, self_state: SelfState, continent: int) -> int:
    border_territories = game.state.get_all_border_territories(
        game.state.get_territories_owned_by(game.state.me.player_id)
    )
    candidate_attackers = union_continent_territories(game, border_territories, self_state.cur_prio[0])
    if len(candidate_attackers) == 0:
        candidate_attackers = intersect_territories(self_state.out_choke_points[self_state.cur_prio[0]], border_territories)
        attacker = sorted(candidate_attackers, key=lambda x: game.state.territories[x].troops, reverse=True)[0]
    return attacker

def get_best_attacker_eliminate(game: Game, player_id: int) -> int:
    border_territories = game.state.get_all_border_territories(
        game.state.get_territories_owned_by(game.state.me.player_id)
    )
    territories = game.state.get_territories_owned_by(player_id)
    player_adj_territories = game.state.get_all_adjacent_territories(territories)
    candidate_attackers = intersect_territories(border_territories, player_adj_territories)

    if len(candidate_attackers) <= 0:
        return NOT_FOUND

    best_attacker = sorted(candidate_attackers, key=lambda x: game.state.territories[x].troops, reverse=True)[0]
    return best_attacker

def get_priority_target_cont(game: Game, self_state: SelfState, continent: int):
    #TODO: improve targeting
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    target_candidates = list(set(game.state.map.get_continents()[continent]) & set(game.state.get_all_adjacent_territories(my_territories)))
    target_candidates = list(set(target_candidates) - set(my_territories))
    target = target_candidates[0]

    #how to choose target candidates
    target_choke = intersect_territories(target_candidates, self_state.in_choke_points[continent])
    target_non_choke = list(set(target_candidates) - set(target_choke))
    target_non_choke = sorted(target_non_choke, key=lambda x: len(game.state.map.get_adjacent_to(x))) #capture least neighbours
        
    #get non-choke first
    if len(target_non_choke) > 0:
        target = target_non_choke[0]
    elif len(target_choke) > 0:
        target = target_choke[0]
    return target

# Prioritize territories with least adjacent 'friendly' (that player's) territory
def get_priority_target_elim(game: Game, self_state: SelfState, attacker: int, target_player_id: int) -> int:
    target_candidates = get_adjacent_player_territories(game, attacker, target_player_id)
    target = sorted(target_candidates, key=lambda x: len(get_adjacent_player_territories(game, x, target_player_id)))[0]

    return target

def get_adjacent_enemy_territories(game: Game, self_state: SelfState, territory: int) -> list[int]:
    adjacent_territory = game.state.map.get_adjacent_to(territory)
    owned_territories = game.state.get_territories_owned_by(game.state.me.player_id)

    return list(set(adjacent_territory) - set(owned_territories))

def get_adjacent_player_territories(game: Game, territory: int, player_id: int) -> list[int]:
    adjacent_territory = game.state.map.get_adjacent_to(territory)
    player_territories = game.state.get_territories_owned_by(player_id)

    return list(set(adjacent_territory) & set(player_territories))

def get_adjacent_territories_in_cluster(game: Game, territory: int, cluster: list[int]) -> list[int]:
    adjacent_territory = game.state.map.get_adjacent_to(territory)
    #print('adj_t: ', adjacent_territory, flush=True)
    #print('clt: ', cluster, flush=True)
    #print('result: ', list(set(adjacent_territory) & set(cluster)), flush=True)
    return list(set(adjacent_territory) & set(cluster))

def get_eliminate_player_difficulty_score(game: Game, player_id: int) -> int:
    #territory_count = len(game.state.get_territories_owned_by(player_id))
    #TODO: maybe can get from player.troops_remaining?
    #troop_count = sum([game.state.territories[x].troops for x in game.state.get_territories_owned_by(player_id)])
    #return troop_count + (territory_count * TERRITORY_SCORE) + ELIM_MOD
    territories = game.state.get_territories_owned_by(player_id)
    return get_cluster_difficulty_score(game, territories)

def get_player_clusters(game: Game, player_id: int) -> list[list[int]]:
    player_territories = game.state.get_territories_owned_by(player_id)
        
    return get_clusters(game, player_territories)

def get_continent_clusters(game: Game, continent_id: int) -> list[list[int]]:
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    continent_territories = game.state.map.get_continents()[continent_id]
    unowned = list(set(continent_territories) - set(my_territories))

    return get_clusters(game, unowned)

def get_clusters(game: Game, territories: list[int]) -> list[list[int]]:
    clusters = []
    if len(territories) <=0:
        return []
    current = territories[0]
    unseen = set(territories)
    unseen.remove(current)

    #loop over all clusters
    while True:
        cluster = [current]
        queue = deque()
        queue.appendleft(current)

        while True:
            adjacent_friendlies = get_adjacent_territories_in_cluster(game, current, territories)
            for adjacent in adjacent_friendlies:
                if adjacent in unseen:
                    unseen.remove(adjacent)
                    queue.append(adjacent)
                    cluster.append(adjacent)
            if len(queue) <= 0:
                break
            current = queue.pop()

        clusters.append(cluster)
        if len(unseen) <= 0:
            break
        current = unseen.pop()
        
    return clusters

def generate_priority_clusters(game: Game, self_state: SelfState, deployable_troops: int) -> list[TargetCluster]:
    start_time = time()
    print("func_gen_prio_clus_start --- %s seconds ---" % (time() - start_time), flush=True)

    result: list[TargetCluster] = []

    cluster_dict: dict[int, TargetCluster] = {} #cluster id to cluster
    booked_troops_count: dict[int, int] = defaultdict(lambda: 0) #territory id to num. of troops booked
    cur_cluster_id = 0

    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    #border_territories = game.state.get_all_border_territories(my_territories)

    if game.state.card_sets_redeemed > CARDS_REDEEMED_LATE_GAME:
        eliminate_player_difficulty_score = {}
        weakest_players = []
        for player in game.state.players.values():
            if player.player_id == game.state.me.player_id or not player.alive:
                continue # Ignore if player is us or knocked out

            difficulty_score = get_eliminate_player_difficulty_score(game, player.player_id)
            my_troops = get_troops_in_cluster(game, my_territories)
            if difficulty_score <= my_troops + deployable_troops:
                weakest_players.append(player.player_id)
                eliminate_player_difficulty_score[player.player_id] = difficulty_score
        weakest_players = sorted(weakest_players, key=lambda x: eliminate_player_difficulty_score[x])

        for player_id in weakest_players:
            #skip_player_flag = False
            updated_cluster_ids: list[int] = []
            print("start_get_clusters --- %s seconds ---" % (time() - start_time), flush=True)
            clusters = get_player_clusters(game, player_id)
            print("end_get_clusters --- %s seconds ---" % (time() - start_time), flush=True)
            for cluster in clusters:
                #if skip_player_flag:
                #    break
                print("start_get_best_path --- %s seconds ---" % (time() - start_time), flush=True)
                best_path = get_best_path_from_score(game, cluster, set(), booked_troops_count)
                print("end_get_best_path --- %s seconds ---" % (time() - start_time), flush=True)
                new_cluster = list(set(cluster).union(set(best_path[0][1:])))
                cluster_score = get_cluster_difficulty_score(game, new_cluster) #lower score better
                #wc_cluster_score = get_cluster_worst_case_difficulty_score(game, cluster) #lower score better
                cluster_attacker = get_cluster_best_attacker(game, new_cluster)

                print('\ncluster: ', new_cluster, flush=True)
                print('cluster_score', cluster_score, flush=True)
                print('attacker', cluster_attacker, flush=True)
                attacker_troops = game.state.territories[cluster_attacker].troops
                target_cluster = TargetCluster(
                    cur_cluster_id, new_cluster, cluster, cluster_attacker, cluster_score, max(cluster_score-(attacker_troops-booked_troops_count[cluster_attacker]), 0), CL_TYPE_PLAYER
                )
                #target_cluster.wc_recommended_troops = max(wc_cluster_score-(attacker_troops-booked_troops_count[cluster_attacker]), 0)
                
                cluster_dict[cur_cluster_id] = target_cluster
                booked_troops_count[cluster_attacker] += cluster_score
                updated_cluster_ids.append(cur_cluster_id)
                cur_cluster_id += 1

            #if skip_player_flag:
            #    continue

            if sum(cluster_dict[x].recommended_troops for x in updated_cluster_ids) <= deployable_troops:
                updated_cluster_ids = sorted(updated_cluster_ids, 
                                             key=lambda x: len(intersect_territories(game.state.get_all_adjacent_territories(cluster_dict[x].cluster), my_territories))
                                            )
                for id in updated_cluster_ids:
                    cluster_dict[id].commit = True
                    result.append(cluster_dict[id])
                    deployable_troops -= cluster_dict[id].recommended_troops
            else:
                for id in updated_cluster_ids:
                    booked_troops_count[cluster_dict[id].attacker] -= cluster_dict[id].difficulty_score

    print("func_done_gen_player_clusters --- %s seconds ---" % (time() - start_time), flush=True)
    ####################################################################################################
    # Create clusters for continents (remake)
    # Check for owned continents
    # If no owned continents, choose continent that we are most likely to takeover, and insert it into cluster
    # If we have an owned continent, loop over all unowned continents
    # Target the continent we are most likely to takeover
    #   - Get cluster difficulty score, check if we are able to takeover the entire continent
    #     - Check continent's outchokes. How many troops are there + predict how many troops they will get
    #     - Don't takeover if we can't defend afterwards
    #   - If we can't, attempt to take the weakest territory in that continent, to draw a card (CL_TYPE_FORCED)
    # PHASE 2 (CL_TYPE_DISRUPT)
    #   - Check continents adjacent to our owned continents, IF THEY ARE COMPLETELY OWNED BY ANOTHER PLAYER
    #   - If they are, check the amount of troops in the in-choke
    #   - Take the in-choke if it is weak (create cluster for that in-choke)
    #     - This makes sure the player doesn't get the continent bonus, at low cost to us
    ####################################################################################################

    #TODO IMPLEMENT CACHING HERE !!!!!
    candidate_continents = set(game.state.map.get_continents().keys())
    remaining_continents = candidate_continents # For disrupt attack
    if game.state.card_sets_redeemed <= CARDS_REDEEMED_LATE_GAME and get_num_remaining_player(game) > 2:
        owned_cont = []
        for cont in set(game.state.map.get_continents().keys()):
            if get_continent_percent_owned(game, cont) >= 1.0:
                owned_cont.append(cont)

        if len(owned_cont) <= 0:
            # Find continent that we can most likely takeover
            # Get continent territory cluster, append to out-choke
            best_candidate = 3
            best_score = 0.0
            for c in game.state.map.get_continents().keys():
                candidate_cluster = game.state.map.get_continents()[c] + self_state.out_choke_points[c]
                score = get_cluster_percent_owned_complex(game, candidate_cluster, deployable_troops)
                if score > best_score:
                    best_score = score
                    best_candidate = c
            candidate_continents = set([best_candidate])
        else:
            candidate_continents = set()
            for cont in owned_cont:
                candidate_continents = candidate_continents | set(self_state.cont_adj[cont])
                candidate_continents = candidate_continents - set(owned_cont)
    

    continent_difficulty_score_dict: dict[int, int] = {}
    cluster_troop_diff_dict: dict[int, int] = {}
    continent_cluster_ids_dict: dict[int, list[int]] = {}
    print('CANDIDATE CONTS: ', candidate_continents, flush=True)
    for continent_id in candidate_continents:
        updated_cluster_ids: list[int] = []
        print("start_get_continent_clusters --- %s seconds ---" % (time() - start_time), flush=True)
        clusters = get_continent_clusters(game, continent_id)
        print("end_get_continent_clusters --- %s seconds ---" % (time() - start_time), flush=True)
        if len(clusters) <= 0:
            continue

        for cluster in clusters:
            print("start_get_best_path --- %s seconds ---" % (time() - start_time), flush=True)
            best_path = get_best_path_from_score(game, cluster, set(), booked_troops_count)
            print("end_get_best_path_clusters --- %s seconds ---" % (time() - start_time), flush=True)
            new_cluster = list(set(cluster).union(set(best_path[0][1:])))
            cluster_score = get_cluster_difficulty_score(game, new_cluster) #lower score better
            cluster_attacker = get_cluster_best_attacker(game, new_cluster)
            attacker_troops = game.state.territories[cluster_attacker].troops
            target_cluster = TargetCluster(
                cur_cluster_id, new_cluster, cluster, cluster_attacker, cluster_score, max(cluster_score-(attacker_troops-booked_troops_count[cluster_attacker]), 0), CL_TYPE_CONTINENT
            )
            cluster_troop_diff_dict[cur_cluster_id] = cluster_score-(attacker_troops-booked_troops_count[cluster_attacker])
            target_cluster.continent = continent_id
            print('\ncont cluster: ', new_cluster, flush=True)
            print('cluster_score', cluster_score, flush=True)
            print('attacker', cluster_attacker, flush=True)

            #continent_hold_difficulty = 0
            if game.state.card_sets_redeemed <= CARDS_REDEEMED_LATE_GAME:
                adjacent_to_cluster = game.state.get_all_adjacent_territories(cluster)
                out_choke_adjacent_to_cluster = intersect_territories(self_state.out_choke_points[continent_id], adjacent_to_cluster)
                for c in out_choke_adjacent_to_cluster:
                    if game.state.territories[c].occupier != game.state.me.player_id:
                        adjacent_in_chokes = get_adjacent_territories_in_cluster(game, c, game.state.map.get_continents()[continent_id])
                        defended = True
                        for in_chokes in adjacent_in_chokes:
                            if game.state.territories[in_chokes].occupier != game.state.me.player_id:
                                defended = False
                        
                        if not defended:
                            #TODO: Add logic to consider amount of troops enemies will get next turn
                            target_cluster.difficulty_score += game.state.territories[c].troops - 1
                            target_cluster.recommended_troops = max(target_cluster.difficulty_score-(attacker_troops-booked_troops_count[cluster_attacker]), 0)
                            cluster_troop_diff_dict[cur_cluster_id] = target_cluster.difficulty_score-(attacker_troops-booked_troops_count[cluster_attacker])

            cluster_dict[cur_cluster_id] = target_cluster
            #booked_troops_count[cluster_attacker] += cluster_score
            updated_cluster_ids.append(cur_cluster_id)
            cur_cluster_id += 1


        """
        continent_hold_difficulty = 0
        if game.state.card_sets_redeemed <= CARDS_REDEEMED_LATE_GAME:
            for c in self_state.out_choke_points[continent_id]:
                # Check if outchoke is already defended by our troops
                # If outchoke territory's adjacent in-choke border is not friendly territory, count it
                # else skip
                if game.state.territories[c].occupier != game.state.me.player_id:
                    adjacent_in_chokes = get_adjacent_territories_in_cluster(game, c, game.state.map.get_continents()[continent_id])
                    defended = True
                    for in_chokes in adjacent_in_chokes:
                        if game.state.territories[in_chokes].occupier != game.state.me.player_id:
                            defended = False
                    
                    if not defended:
                        #enemy = game.state.territories[c].occupier
                        #TODO: Add logic to consider amount of troops enemies will get next turn
                        continent_hold_difficulty += game.state.territories[c].troops - 1
        """
        continent_difficulty_score_dict[continent_id] = sum(cluster_troop_diff_dict[x] for x in updated_cluster_ids)# + continent_hold_difficulty
        continent_cluster_ids_dict[continent_id] = updated_cluster_ids
    
    candidate_target_continents = sorted(list(continent_difficulty_score_dict.keys()), key=lambda x: continent_difficulty_score_dict[x])
    print('CLUSTER TROOP DIFF DICT: ', cluster_troop_diff_dict, flush=True)
    print('CONT DIFFSCORE: ', continent_difficulty_score_dict, flush=True)
    print('CANDIDATE TARGET CONTS: ', candidate_target_continents, flush=True)

    # Recalculate difficulty to account for troop booking
    # Need to recalculate after sorting target continents w/ regards to priority
    for continent_id in candidate_target_continents:
        continent_cluster_ids_dict[continent_id] = sorted(continent_cluster_ids_dict[continent_id], 
                                    key=lambda x: len(intersect_territories(game.state.get_all_adjacent_territories(cluster_dict[x].cluster), my_territories))
                                    )
        for id in continent_cluster_ids_dict[continent_id]:
            cluster_score = cluster_dict[id].difficulty_score
            cluster_attacker = cluster_dict[id].attacker
            attacker_troops = game.state.territories[cluster_attacker].troops
            cluster_troop_diff_dict[id] = cluster_score-(attacker_troops-booked_troops_count[cluster_attacker])
            booked_troops_count[cluster_attacker] += cluster_score
            cluster_dict[id].recommended_troops = max(cluster_troop_diff_dict[id], 0)

    #tmp
    for continent_id in candidate_target_continents:
        if continent_difficulty_score_dict[continent_id] <= deployable_troops or get_num_remaining_player(game) <= 2:
            #cont_cluster_ids = sorted(continent_cluster_ids_dict[continent_id], 
            #                            key=lambda x: len(intersect_territories(game.state.get_all_adjacent_territories(cluster_dict[x].cluster), my_territories))
            #                            )
            for id in continent_cluster_ids_dict[continent_id]:
                cluster_dict[id].commit = True
                #booked_troops_count[cluster_dict[id].attacker] += cluster_score
                result.append(cluster_dict[id])
            deployable_troops -= continent_difficulty_score_dict[continent_id]
            remaining_continents.discard(continent_id)
    """
        elif len(get_players_in_continent(game, continent_id)) <= 1:

            # Attempt to disrupt if an enemy owns the entire continent
            # Early game: If cost is very small, attempt disruption (1/2 troop territory)
            #   - Create cluster with continent's in-choke
            #   - Find the best path to it
            #   - Append to result if score is acceptable
            # Late game: When there is only 2 (maybe 3?) players left
            #   - Use all resources to reduce enemy continent bonuses as much as possible, while maintaining our own
            #   - Create cluster path to in-choke?

            cont_in_chokes = self_state.in_choke_points[continent_id]
            best_disrupt_cluster: list[int] = []
            best_disrupt_target = NOT_FOUND
            lowest_diff_score = INF_INT
            for territory in cont_in_chokes:
                print('disrupt: ', territory, flush=True)
                print("dist_time --- %s seconds ---" % (time() - start_time), flush=True)
                best_path = get_best_path_from_score(game, cluster, set(game.state.map.get_continents()[continent_id]), booked_troops_count)
                new_cluster = list(set(cluster).union(set(best_path[0][1:])))
                cluster_score = get_cluster_difficulty_score(game, new_cluster) #lower score better
                if cluster_score < lowest_diff_score:
                    best_disrupt_cluster = new_cluster
                    lowest_diff_score = cluster_score
                    best_disrupt_target = territory
            
            cluster_attacker = get_cluster_best_attacker(game, best_disrupt_cluster)
            attacker_troops = game.state.territories[cluster_attacker].troops
            target_cluster = TargetCluster(
                cur_cluster_id, best_disrupt_cluster, [best_disrupt_target], cluster_attacker, lowest_diff_score, max(lowest_diff_score-(attacker_troops-booked_troops_count[cluster_attacker]), 0), CL_TYPE_DISRUPT
            )
            cluster_dict[cur_cluster_id] = target_cluster
            disrupt_cluster_id = cur_cluster_id
            cur_cluster_id += 1
            if cluster_dict[disrupt_cluster_id].recommended_troops <= deployable_troops:
                cluster_dict[disrupt_cluster_id].commit = True
                result.append(cluster_dict[disrupt_cluster_id])
                deployable_troops -= cluster_dict[disrupt_cluster_id].recommended_troops
    """
    for continent_id in remaining_continents:
        if len(get_players_in_continent(game, continent_id)) <= 1 and get_continent_percent_owned(game, continent_id) >= 1.0:
            #my_adjacent_territories = get_cluster_adjacent_friendly(game, game.state.map.get_continents()[continent_id])
            candidate_targets = intersect_territories(game.state.get_all_adjacent_territories(my_territories), game.state.map.get_continents()[continent_id])
            if len(candidate_targets) <= 0:
                continue
            least_troops_target = min(candidate_targets, key=lambda x: game.state.territories[x].troops)
            cluster_attacker = get_cluster_best_attacker(game, [least_troops_target])
            attacker_troops = game.state.territories[cluster_attacker].troops
            cluster_score = get_cluster_difficulty_score(game, [least_troops_target])
            target_cluster = TargetCluster(
                cur_cluster_id, [least_troops_target], [least_troops_target], cluster_attacker, cluster_score, max(cluster_score-(attacker_troops-booked_troops_count[cluster_attacker]), 0), CL_TYPE_DISRUPT
            )
            cluster_dict[cur_cluster_id] = target_cluster
            cur_cluster_id += 1

            if target_cluster.recommended_troops <= deployable_troops:
                result.append(target_cluster)
                deployable_troops -= target_cluster.recommended_troops

    # Append forced attack cluster if nothing in results
    if len(result) <= 0:
        continent_id = candidate_target_continents[0]
        cluster_id = continent_cluster_ids_dict[continent_id][0]
        target_cluster = cluster_dict[cluster_id]
        target_cluster.type = CL_TYPE_FORCED
        target_cluster.commit = True
        result.append(target_cluster)
        
        #if sum(cluster_dict[x].recommended_troops for x in updated_cluster_ids) <= deployable_troops:
        #    updated_cluster_ids = sorted(updated_cluster_ids, 
        #                                key=lambda x: len(intersect_territories(game.state.get_all_adjacent_territories(cluster_dict[x].cluster), my_territories))
        #                               )
        #    for id in updated_cluster_ids:
        #        cluster_dict[id].commit = True
        #        result.append(cluster_dict[id])
        #        deployable_troops -= cluster_dict[id].recommended_troops
        #else:
        #    for id in updated_cluster_ids:
        #        booked_troops_count[cluster_dict[id].attacker] -= cluster_dict[id].difficulty_score

    print("func_done_gen_continent_clusters --- %s seconds ---" % (time() - start_time), flush=True)

    return result

def get_troops_in_cluster(game: Game, cluster: list[int]) -> int:
    return sum([game.state.territories[x].troops for x in cluster])

def get_most_troops_in_cluster(game: Game, cluster: list[int]) -> int:
    return max(cluster, key=lambda x: game.state.territories[x].troops)

def get_cluster_adjacent_friendly(game: Game, cluster: list[int]) -> list[int]:
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    cluster_adjacent = game.state.get_all_adjacent_territories(cluster)
    return intersect_territories(my_territories, cluster_adjacent)

#assumes cluster has adjacent friendly territory
def get_cluster_best_attacker(game: Game, cluster: list[int]) -> int:
    candidates = get_cluster_adjacent_friendly(game, cluster)
    if len(candidates) <= 0:
        return NOT_FOUND
    return get_most_troops_in_cluster(game, candidates)

def get_cluster_difficulty_score(game: Game, cluster: list[int]) -> int:
    score = ELIM_MOD
    nodes = 0
    for territory in cluster:
        nodes += 1
        troop_count = game.state.territories[territory].troops
        if troop_count == 1 or nodes <= 1:
            score += troop_count
        else:
            score += troop_count + TERRITORY_SCORE
    return score

"""
def get_cluster_worst_case_difficulty_score(game: Game, cluster: list[int]) -> int:
    score = ELIM_MOD_WORST
    
    for territory in cluster:
        troop_count = game.state.territories[territory].troops
        if troop_count == 1:
            score += troop_count
        else:
            score += troop_count + TERRITORY_SCORE
    return score
"""

def is_target_cut_node(game: Game, cluster: list[int], target: int) -> bool:
    if target not in cluster:
        return False
    
    adjacent_territories = game.state.map.get_adjacent_to(target)
    adjacent_cluster_territories = intersect_territories(cluster, adjacent_territories)

    if len(adjacent_cluster_territories) <= 1:
        return False
    tmp_cluster = cluster[:]
    tmp_cluster.remove(target)

    clusters = get_clusters(game, tmp_cluster)

    if len(clusters) <=1:
        return False
    
    return True

def sort_attack_priority(game: Game, cluster: list[int], candidate_targets: list[int]) -> list[int]:
    is_cut_node: list[int] = []
    is_not_cut_node: list[int] = []
    #for target in candidate_targets:
    #    is_cut_node = is_target_cut_node(game, cluster, target)
    #    adjacent_to_target = game.state.map.get_adjacent_to(target)
    
    sorted_targets = sorted(candidate_targets, key= lambda x: len(intersect_territories(game.state.map.get_adjacent_to(x), cluster)))
    for target in sorted_targets:
        if is_target_cut_node(game, cluster, target):
            is_cut_node.append(target)
        else:
            is_not_cut_node.append(target)

    print('sort_prio_cluster: ', cluster, flush=True)
    print('is_not_cut_node: ', is_cut_node, flush=True)
    print('is_cut: ', is_cut_node, flush=True)
    
    return is_not_cut_node + is_cut_node

def get_path_score(game: Game, path: list[int], path_score: int) -> int:
    if len(path) <= 0:
        return NEG_INF_INT
    #print(path, ':', path_score)
    return game.state.territories[path[0]].troops - path_score

def get_best_path_from_score(game: Game, cluster: list[int], banned: set[int], booked_troops_count: dict[int, int]) -> tuple[list[int], int]:
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    border_territories = game.state.get_all_border_territories(my_territories)

    # Check if adjacent territories are good enough
    adjacent_to_cluster = intersect_territories(game.state.get_all_adjacent_territories(cluster), border_territories)
    adjacent_to_cluster = sorted(adjacent_to_cluster, key=lambda x: game.state.territories[x].troops)
    for territory in adjacent_to_cluster:
        cluster_score = get_cluster_difficulty_score(game, cluster)
        cluster_attacker = get_cluster_best_attacker(game, cluster)
        if cluster_attacker == NOT_FOUND:
            continue
        attacker_troops = game.state.territories[cluster_attacker].troops
        if cluster_score <= (attacker_troops-booked_troops_count[cluster_attacker]):
            return ([territory]+cluster, 0)


    tmp: list[tuple[list[int], int]] = []
    path_tuple = get_best_path_to_cluster(game, cluster, border_territories, banned)
    tmp.append(path_tuple)
    #if len(path_tuple[0]) > 0:
    #    adjacent_borders = get_adjacent_player_territories(game, path_tuple[0][0], game.state.me.player_id)
    #    tmp.append(get_best_path_to_cluster(game, cluster, adjacent_borders, set(my_territories) - set(adjacent_borders) - banned))
    most_troops_territory = max(border_territories, key=lambda x: game.state.territories[x].troops)
    tmp.append(get_best_path_to_cluster(game, cluster, [most_troops_territory], set(my_territories) - {most_troops_territory} - banned))

    for tpl in tmp:
        print('\nori-cluster: ', cluster, flush=True)
        print('score candidates: ', tpl, flush=True)

    # get_path_score subtracts attacker troops with difficulty score, sort to get highest
    best_path = max(tmp, key=lambda x: get_path_score(game, x[0], x[1]))
    return best_path

def get_highest_priority_starting_territory(game: Game, self_state: SelfState, unclaimed_candidates: list[int], prio_conts: set) -> tuple[int, int]:
    #my_conts = get_my_continents(game, self_state)
    #adj_cont = self_state.cont_adj[cont]
    #in_choke = self_state.in_choke_points[cont]

    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    adjacent_territories = game.state.get_all_adjacent_territories(my_territories)
    my_continents = get_my_continents(game) # All continents in owned continents
    unclaimed_territories = game.state.get_territories_owned_by(None)

    overpop_cont = set()
    non_empty_cont = set()
    for i in range(6):
        cont_terr = game.state.map.get_continents()[i]
        cont_available = intersect_territories(cont_terr, unclaimed_territories)
        enemy_count = len(get_players_in_continent(game, i))

        if i in my_continents:
            enemy_count -= 1
        if enemy_count >= 2:
            overpop_cont.add(i)

        if len(cont_available) != len(cont_terr):
            non_empty_cont.add(i)

    prio_adj_out_choke = [] # adjacent continent's out-choke where there are other players
    for nec in non_empty_cont:
        prio_adj_out_choke = prio_adj_out_choke + self_state.out_choke_points[nec]

    prio_in_choke = [] # in-choke of my continent
    for pc in prio_conts:
        prio_in_choke = self_state.in_choke_points[pc]

    prio_out_choke = [] # out-choke of my continent
    for pc in prio_conts:
       prio_in_choke = self_state.in_choke_points[pc]

    candidate_score = {}
    for territory in unclaimed_candidates:
        territory_continent = get_territory_continent(territory)
        
        if territory in prio_in_choke and territory in prio_adj_out_choke:
            candidate_score[territory] = 6
        elif territory in prio_in_choke:
            candidate_score[territory] = 5
        elif territory_continent in my_continents and territory in adjacent_territories:
            candidate_score[territory] = 4
        elif territory_continent in my_continents:
            candidate_score[territory] = 3
        elif territory in prio_out_choke:
            candidate_score[territory] = 2
        elif territory in adjacent_territories:
            candidate_score[territory] = 1
        else:
            candidate_score[territory] = NOT_FOUND

    top_candidate = sorted(unclaimed_candidates, key=lambda x: candidate_score[x], reverse=True)[0]
    print('top_c: ', top_candidate, flush=True)
    print('score: ', candidate_score[top_candidate], flush=True)
    return top_candidate, candidate_score[top_candidate]

def get_players_in_continent(game: Game, cont: int) -> set[int]:
    result = set()
    cont_territories = game.state.map.get_continents()[cont]
    for t in cont_territories:
        if game.state.territories[t].occupier != None:
            result.add(game.state.territories[t].occupier)
    return result

def get_num_remaining_player(game: Game) -> int:
    count = 0
    for values in game.state.players.items():
        if values[1].alive:
            count += 1
    return count

def get_strongest_player(game: Game) -> int:
    total_troops_per_player = {}
    for player in game.state.players.values():
        total_troops_per_player[player.player_id] = sum([game.state.territories[x].troops for x in game.state.get_territories_owned_by(player.player_id)])

    most_powerful_player = max(total_troops_per_player.items(), key=lambda x: x[1])[0]
    return most_powerful_player

if __name__ == "__main__":
    main()