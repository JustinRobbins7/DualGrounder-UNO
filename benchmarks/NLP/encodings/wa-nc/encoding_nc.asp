%
% == modules/base/bwd-a.lp ==
%

% BWD-A encoding

% if something is a goal it is potentially interesting
pot(P) :- goal(P).

% if somehing may be required by inference it is also potentially interesting
pot(P) :- inferenceNeeds(_,_,P).

% if something is a goal it is true
true(P) :- goal(P).

% if something is true it must be inferred, or factored/abduced
1 <= { infer(P); fai(P) } <= 1 :- true(P).

% if something is inferred, it is inferred via exactly one rule
1 <= { inferVia(R,P) : mayInferVia(R,P,_) } <= 1 :- infer(P).

% if inference needs something that something is also true
true(Q) :- inferVia(R,P), inferenceNeeds(P,R,Q).

% equivalences
hu(X) :- pot(c(_,X,_)).
hu(X) :- pot(c(_,_,X)).
uhu(X) :- hu(X), not sortname(X).
{ eq(A,B): uhu(A), uhu(B), A != B }.

% equivalence must be reflexive
eq(A,A) :- hu(A).

% equivalence must be symmetric
:- eq(A,B), not eq(B,A).

% equivalence must be transitive
% outsourced into acyc_trans/*.lp encoding modules!

% "A" (factor only with abduced) factoring method 

% factor with abduced, or abduce
fa(P) :- fai(P).

% if two atoms that are either factored or abduced unify, the lexicographic larger one is considered factored
factorCluster(c(P,S2,O2),c(P,S1,O1)) :-
  fa(c(P,S1,O1)), fa(c(P,S2,O2)), (S1,O1) < (S2,O2), eq(S1,S2), eq(O1,O2).
% which element in a cluster has no element above?
factorClusterAbove(A) :- factorCluster(A,_).
% factor all elements of the cluster to that element
% (this achieves a canonicalization and symmetry breaking)
factorVia(A,B) :- factorCluster(A,B), not factorClusterAbove(B).

factor(X) :- factorVia(X,_).
% the others are abduced
abduce(X) :- fa(X), not factor(X).

%
% == modules/obj/wa.lp ==
%

% WA objective (Weighted Abduction)

% pcost(Atom,Cost) -> potential cost

% we assume goals with cost 100
pcost(P,100) :- goal(P).

% if we infer P via rule R with N body atoms
% -> bodies sum up to 1.2 = 6/5
% -> potential cost of each body Q defined like this
pcost(Q,MC) :- pcost(P,C), MC = #max { (C*6/5)/N ; 1 },
  inferVia(R,P), inferenceNeeds(P,R,Q), numberOfBodies(R,N).

% if we factor something we propagate the minimum
% factorVia(P,Q) means Q obtains minimum cost of all P
pcost(Q,C) :- factorVia(P,Q), pcost(P,C).

% cost(Atom,Cost)  -> actual cost = minimum of all pcost
cost(P,C) :- abduce(P), C = #min { IC : pcost(P,IC) }, C != #sup.

% minimize cost of abduced
:~ cost(P,C). [C@1,P]

%
% == modules/acyc-trans/eq-ondemand.lp ==
%

% Ensure transitivity of the eq/2 relation in on-demand constraints

% activate on-demand constraint processing in run.py
eqondemand.

%
% == modules/skolem/flexskolem-infty.lp ==
%

% Infinite Skolemization but disallow recursive axioms.

% No facts here, because this is the default mode of run.py.

%
% == modules/base/projection.lp ==
%


#show true/1. #show abduce/1. #show infer/1. #show cost/2. #show factor/1.
#show inferVia/2. #show inferenceNeeds/3. #show factorVia/2.
#show eq/2. #show pcost/2.

%
% == kb/sortnames.lp ==
%

% KB rewriting for sortnames
sortname(taxi).
sortname(partying).
sortname(pointing).
sortname(straw).
sortname(money).
sortname(liquor).
sortname(going_by_plane).
sortname(valuable).
sortname(seat).
sortname(jewelry).
sortname(getting_on).
sortname(smarket_shopping).
sortname(uniform).
sortname(skirt).
sortname(ticket).
sortname(shopping_place).
sortname(physical).
sortname(liquor_store).
sortname(flower).
sortname(shirt).
sortname(working).
sortname(giving).
sortname(prison).
sortname(milk).
sortname(jogging).
sortname(any).
sortname(going).
sortname(vehicle).
sortname(finding).
sortname(ingesting).
sortname(bourbon).
sortname(knife).
sortname(shopping).
sortname(sitting).
sortname(food).
sortname(shelf).
sortname(going_by_bus).
sortname(trousers).
sortname(park).
sortname(liqst_shopping).
sortname(action).
sortname(ordering).
sortname(plane).
sortname(putting).
sortname(milkshake).
sortname(robbing).
sortname(drinking).
sortname(getting_off).
sortname(buying).
sortname(bread).
sortname(paying).
sortname(smarket).
sortname(school).
sortname(gun).
sortname(gift).
sortname(getting).
sortname(airport).
sortname(weapon).
sortname(restaurant).
sortname(packing).
sortname(bus_station).
sortname(going_by_vehicle).
sortname(bag).
sortname(token).
sortname(suitcase).
sortname(place).
sortname(going_by_taxi).
sortname(rest_dining).
sortname(apparel).
sortname(bus).
sortname(courting).

%
% == kb/bwd-uf-skolem.lp ==
%

% KB rewriting BWD with Uninterpreted Function Skolemization
comment("inst(G,going) <- inst(S,shopping), go_step(S,G)").
mayInferVia(r0,c(inst,G,going),l(S)) :- pot(c(inst,G,going)), S = s(G,1).
numberOfBodies(r0,2).
inferenceNeeds(c(inst,G,going),r0,c(inst,S,shopping)) :- mayInferVia(r0,c(inst,G,going),l(S)).
inferenceNeeds(c(inst,G,going),r0,c(go_step,S,G)) :- mayInferVia(r0,c(inst,G,going),l(S)).
comment("goer(G,P) <- inst(S,shopping), go_step(S,G), shopper(S,P)").
mayInferVia(r1,c(goer,G,P),l(S)) :- pot(c(goer,G,P)), S = s(P,G,2).
numberOfBodies(r1,3).
inferenceNeeds(c(goer,G,P),r1,c(inst,S,shopping)) :- mayInferVia(r1,c(goer,G,P),l(S)).
inferenceNeeds(c(goer,G,P),r1,c(go_step,S,G)) :- mayInferVia(r1,c(goer,G,P),l(S)).
inferenceNeeds(c(goer,G,P),r1,c(shopper,S,P)) :- mayInferVia(r1,c(goer,G,P),l(S)).
comment("dest_go(G,Str) <- inst(S,shopping), go_step(S,G), store(S,Str)").
mayInferVia(r2,c(dest_go,G,Str),l(S)) :- pot(c(dest_go,G,Str)), S = s(Str,G,3).
numberOfBodies(r2,3).
inferenceNeeds(c(dest_go,G,Str),r2,c(inst,S,shopping)) :- mayInferVia(r2,c(dest_go,G,Str),l(S)).
inferenceNeeds(c(dest_go,G,Str),r2,c(go_step,S,G)) :- mayInferVia(r2,c(dest_go,G,Str),l(S)).
inferenceNeeds(c(dest_go,G,Str),r2,c(store,S,Str)) :- mayInferVia(r2,c(dest_go,G,Str),l(S)).
comment("inst(Sp,shopping_place) <- inst(S,shopping), store(S,Sp)").
mayInferVia(r3,c(inst,Sp,shopping_place),l(S)) :- pot(c(inst,Sp,shopping_place)), S = s(Sp,4).
numberOfBodies(r3,2).
inferenceNeeds(c(inst,Sp,shopping_place),r3,c(inst,S,shopping)) :- mayInferVia(r3,c(inst,Sp,shopping_place),l(S)).
inferenceNeeds(c(inst,Sp,shopping_place),r3,c(store,S,Sp)) :- mayInferVia(r3,c(inst,Sp,shopping_place),l(S)).
comment("inst(F,finding) <- inst(S,shopping), find_step(S,F)").
mayInferVia(r4,c(inst,F,finding),l(S)) :- pot(c(inst,F,finding)), S = s(F,5).
numberOfBodies(r4,2).
inferenceNeeds(c(inst,F,finding),r4,c(inst,S,shopping)) :- mayInferVia(r4,c(inst,F,finding),l(S)).
inferenceNeeds(c(inst,F,finding),r4,c(find_step,S,F)) :- mayInferVia(r4,c(inst,F,finding),l(S)).
comment("finder(F,A) <- inst(S,shopping), find_step(S,F), shopper(S,A)").
mayInferVia(r5,c(finder,F,A),l(S)) :- pot(c(finder,F,A)), S = s(A,F,6).
numberOfBodies(r5,3).
inferenceNeeds(c(finder,F,A),r5,c(inst,S,shopping)) :- mayInferVia(r5,c(finder,F,A),l(S)).
inferenceNeeds(c(finder,F,A),r5,c(find_step,S,F)) :- mayInferVia(r5,c(finder,F,A),l(S)).
inferenceNeeds(c(finder,F,A),r5,c(shopper,S,A)) :- mayInferVia(r5,c(finder,F,A),l(S)).
comment("thing_found(F,Tf) <- inst(S,shopping), find_step(S,F), thing_shopped_for(S,Tf)").
mayInferVia(r6,c(thing_found,F,Tf),l(S)) :- pot(c(thing_found,F,Tf)), S = s(Tf,F,7).
numberOfBodies(r6,3).
inferenceNeeds(c(thing_found,F,Tf),r6,c(inst,S,shopping)) :- mayInferVia(r6,c(thing_found,F,Tf),l(S)).
inferenceNeeds(c(thing_found,F,Tf),r6,c(find_step,S,F)) :- mayInferVia(r6,c(thing_found,F,Tf),l(S)).
inferenceNeeds(c(thing_found,F,Tf),r6,c(thing_shopped_for,S,Tf)) :- mayInferVia(r6,c(thing_found,F,Tf),l(S)).
comment("inst(B,buying) <- inst(S,shopping), buy_step(S,B)").
mayInferVia(r7,c(inst,B,buying),l(S)) :- pot(c(inst,B,buying)), S = s(B,8).
numberOfBodies(r7,2).
inferenceNeeds(c(inst,B,buying),r7,c(inst,S,shopping)) :- mayInferVia(r7,c(inst,B,buying),l(S)).
inferenceNeeds(c(inst,B,buying),r7,c(buy_step,S,B)) :- mayInferVia(r7,c(inst,B,buying),l(S)).
comment("buyer(B,P) <- inst(S,shopping), buy_step(S,B), shopper(S,P)").
mayInferVia(r8,c(buyer,B,P),l(S)) :- pot(c(buyer,B,P)), S = s(P,B,9).
numberOfBodies(r8,3).
inferenceNeeds(c(buyer,B,P),r8,c(inst,S,shopping)) :- mayInferVia(r8,c(buyer,B,P),l(S)).
inferenceNeeds(c(buyer,B,P),r8,c(buy_step,S,B)) :- mayInferVia(r8,c(buyer,B,P),l(S)).
inferenceNeeds(c(buyer,B,P),r8,c(shopper,S,P)) :- mayInferVia(r8,c(buyer,B,P),l(S)).
comment("thing_bought(B,Tb) <- inst(S,shopping), buy_step(S,B), thing_shopped_for(S,Tb)").
mayInferVia(r9,c(thing_bought,B,Tb),l(S)) :- pot(c(thing_bought,B,Tb)), S = s(B,Tb,10).
numberOfBodies(r9,3).
inferenceNeeds(c(thing_bought,B,Tb),r9,c(inst,S,shopping)) :- mayInferVia(r9,c(thing_bought,B,Tb),l(S)).
inferenceNeeds(c(thing_bought,B,Tb),r9,c(buy_step,S,B)) :- mayInferVia(r9,c(thing_bought,B,Tb),l(S)).
inferenceNeeds(c(thing_bought,B,Tb),r9,c(thing_shopped_for,S,Tb)) :- mayInferVia(r9,c(thing_bought,B,Tb),l(S)).
comment("inst(P,paying) <- inst(B,buying), pay_step(B,P)").
mayInferVia(r10,c(inst,P,paying),l(B)) :- pot(c(inst,P,paying)), B = s(P,11).
numberOfBodies(r10,2).
inferenceNeeds(c(inst,P,paying),r10,c(inst,B,buying)) :- mayInferVia(r10,c(inst,P,paying),l(B)).
inferenceNeeds(c(inst,P,paying),r10,c(pay_step,B,P)) :- mayInferVia(r10,c(inst,P,paying),l(B)).
comment("payer(P,A) <- inst(B,buying), pay_step(B,P), buyer(B,A)").
mayInferVia(r11,c(payer,P,A),l(B)) :- pot(c(payer,P,A)), B = s(A,P,12).
numberOfBodies(r11,3).
inferenceNeeds(c(payer,P,A),r11,c(inst,B,buying)) :- mayInferVia(r11,c(payer,P,A),l(B)).
inferenceNeeds(c(payer,P,A),r11,c(pay_step,B,P)) :- mayInferVia(r11,c(payer,P,A),l(B)).
inferenceNeeds(c(payer,P,A),r11,c(buyer,B,A)) :- mayInferVia(r11,c(payer,P,A),l(B)).
comment("thing_paid(P,Tp) <- inst(B,buying), pay_step(B,P), thing_bought(B,Tp)").
mayInferVia(r12,c(thing_paid,P,Tp),l(B)) :- pot(c(thing_paid,P,Tp)), B = s(P,Tp,13).
numberOfBodies(r12,3).
inferenceNeeds(c(thing_paid,P,Tp),r12,c(inst,B,buying)) :- mayInferVia(r12,c(thing_paid,P,Tp),l(B)).
inferenceNeeds(c(thing_paid,P,Tp),r12,c(pay_step,B,P)) :- mayInferVia(r12,c(thing_paid,P,Tp),l(B)).
inferenceNeeds(c(thing_paid,P,Tp),r12,c(thing_bought,B,Tp)) :- mayInferVia(r12,c(thing_paid,P,Tp),l(B)).
comment("inst(Str,smarket) <- inst(S,smarket_shopping), store(S,Str)").
mayInferVia(r13,c(inst,Str,smarket),l(S)) :- pot(c(inst,Str,smarket)), S = s(Str,14).
numberOfBodies(r13,2).
inferenceNeeds(c(inst,Str,smarket),r13,c(inst,S,smarket_shopping)) :- mayInferVia(r13,c(inst,Str,smarket),l(S)).
inferenceNeeds(c(inst,Str,smarket),r13,c(store,S,Str)) :- mayInferVia(r13,c(inst,Str,smarket),l(S)).
comment("inst(F,food) <- inst(S,smarket_shopping), thing_shopped_for(S,F)").
mayInferVia(r14,c(inst,F,food),l(S)) :- pot(c(inst,F,food)), S = s(F,15).
numberOfBodies(r14,2).
inferenceNeeds(c(inst,F,food),r14,c(inst,S,smarket_shopping)) :- mayInferVia(r14,c(inst,F,food),l(S)).
inferenceNeeds(c(inst,F,food),r14,c(thing_shopped_for,S,F)) :- mayInferVia(r14,c(inst,F,food),l(S)).
comment("inst(Ls,liquor_store) <- inst(S,liqst_shopping), store(S,Ls)").
mayInferVia(r15,c(inst,Ls,liquor_store),l(S)) :- pot(c(inst,Ls,liquor_store)), S = s(Ls,16).
numberOfBodies(r15,2).
inferenceNeeds(c(inst,Ls,liquor_store),r15,c(inst,S,liqst_shopping)) :- mayInferVia(r15,c(inst,Ls,liquor_store),l(S)).
inferenceNeeds(c(inst,Ls,liquor_store),r15,c(store,S,Ls)) :- mayInferVia(r15,c(inst,Ls,liquor_store),l(S)).
comment("inst(L,liquor) <- inst(S,liqst_shopping), thing_shopped_for(S,L)").
mayInferVia(r16,c(inst,L,liquor),l(S)) :- pot(c(inst,L,liquor)), S = s(L,17).
numberOfBodies(r16,2).
inferenceNeeds(c(inst,L,liquor),r16,c(inst,S,liqst_shopping)) :- mayInferVia(r16,c(inst,L,liquor),l(S)).
inferenceNeeds(c(inst,L,liquor),r16,c(thing_shopped_for,S,L)) :- mayInferVia(r16,c(inst,L,liquor),l(S)).
comment("inst(G,getting) <- inst(R,robbing), get_weapon_step(R,G)").
mayInferVia(r17,c(inst,G,getting),l(R)) :- pot(c(inst,G,getting)), R = s(G,18).
numberOfBodies(r17,2).
inferenceNeeds(c(inst,G,getting),r17,c(inst,R,robbing)) :- mayInferVia(r17,c(inst,G,getting),l(R)).
inferenceNeeds(c(inst,G,getting),r17,c(get_weapon_step,R,G)) :- mayInferVia(r17,c(inst,G,getting),l(R)).
comment("agent_get(G,A) <- inst(R,robbing), get_weapon_step(R,G), robber(R,A)").
mayInferVia(r18,c(agent_get,G,A),l(R)) :- pot(c(agent_get,G,A)), R = s(A,G,19).
numberOfBodies(r18,3).
inferenceNeeds(c(agent_get,G,A),r18,c(inst,R,robbing)) :- mayInferVia(r18,c(agent_get,G,A),l(R)).
inferenceNeeds(c(agent_get,G,A),r18,c(get_weapon_step,R,G)) :- mayInferVia(r18,c(agent_get,G,A),l(R)).
inferenceNeeds(c(agent_get,G,A),r18,c(robber,R,A)) :- mayInferVia(r18,c(agent_get,G,A),l(R)).
comment("patient_get(G,W) <- inst(R,robbing), get_weapon_step(R,G), weapon_rob(R,W)").
mayInferVia(r19,c(patient_get,G,W),l(R)) :- pot(c(patient_get,G,W)), R = s(W,G,20).
numberOfBodies(r19,3).
inferenceNeeds(c(patient_get,G,W),r19,c(inst,R,robbing)) :- mayInferVia(r19,c(patient_get,G,W),l(R)).
inferenceNeeds(c(patient_get,G,W),r19,c(get_weapon_step,R,G)) :- mayInferVia(r19,c(patient_get,G,W),l(R)).
inferenceNeeds(c(patient_get,G,W),r19,c(weapon_rob,R,W)) :- mayInferVia(r19,c(patient_get,G,W),l(R)).
comment("inst(G,going) <- inst(R,robbing), go_step(R,G)").
mayInferVia(r20,c(inst,G,going),l(R)) :- pot(c(inst,G,going)), R = s(G,21).
numberOfBodies(r20,2).
inferenceNeeds(c(inst,G,going),r20,c(inst,R,robbing)) :- mayInferVia(r20,c(inst,G,going),l(R)).
inferenceNeeds(c(inst,G,going),r20,c(go_step,R,G)) :- mayInferVia(r20,c(inst,G,going),l(R)).
comment("goer(G,A) <- inst(R,robbing), go_step(R,G), robber(R,A)").
mayInferVia(r21,c(goer,G,A),l(R)) :- pot(c(goer,G,A)), R = s(A,G,22).
numberOfBodies(r21,3).
inferenceNeeds(c(goer,G,A),r21,c(inst,R,robbing)) :- mayInferVia(r21,c(goer,G,A),l(R)).
inferenceNeeds(c(goer,G,A),r21,c(go_step,R,G)) :- mayInferVia(r21,c(goer,G,A),l(R)).
inferenceNeeds(c(goer,G,A),r21,c(robber,R,A)) :- mayInferVia(r21,c(goer,G,A),l(R)).
comment("dest_go(G,P) <- inst(R,robbing), go_step(R,G), place_rob(R,P)").
mayInferVia(r22,c(dest_go,G,P),l(R)) :- pot(c(dest_go,G,P)), R = s(P,G,23).
numberOfBodies(r22,3).
inferenceNeeds(c(dest_go,G,P),r22,c(inst,R,robbing)) :- mayInferVia(r22,c(dest_go,G,P),l(R)).
inferenceNeeds(c(dest_go,G,P),r22,c(go_step,R,G)) :- mayInferVia(r22,c(dest_go,G,P),l(R)).
inferenceNeeds(c(dest_go,G,P),r22,c(place_rob,R,P)) :- mayInferVia(r22,c(dest_go,G,P),l(R)).
comment("inst(P,pointing) <- inst(R,robbing), point_weapon_step(R,P)").
mayInferVia(r23,c(inst,P,pointing),l(R)) :- pot(c(inst,P,pointing)), R = s(P,24).
numberOfBodies(r23,2).
inferenceNeeds(c(inst,P,pointing),r23,c(inst,R,robbing)) :- mayInferVia(r23,c(inst,P,pointing),l(R)).
inferenceNeeds(c(inst,P,pointing),r23,c(point_weapon_step,R,P)) :- mayInferVia(r23,c(inst,P,pointing),l(R)).
comment("agent_point(P,A) <- inst(R,robbing), point_weapon_step(R,P), robber(R,A)").
mayInferVia(r24,c(agent_point,P,A),l(R)) :- pot(c(agent_point,P,A)), R = s(A,P,25).
numberOfBodies(r24,3).
inferenceNeeds(c(agent_point,P,A),r24,c(inst,R,robbing)) :- mayInferVia(r24,c(agent_point,P,A),l(R)).
inferenceNeeds(c(agent_point,P,A),r24,c(point_weapon_step,R,P)) :- mayInferVia(r24,c(agent_point,P,A),l(R)).
inferenceNeeds(c(agent_point,P,A),r24,c(robber,R,A)) :- mayInferVia(r24,c(agent_point,P,A),l(R)).
comment("patient_point(P,A) <- inst(R,robbing), point_weapon_step(R,P), victim_rob(R,A)").
mayInferVia(r25,c(patient_point,P,A),l(R)) :- pot(c(patient_point,P,A)), R = s(A,P,26).
numberOfBodies(r25,3).
inferenceNeeds(c(patient_point,P,A),r25,c(inst,R,robbing)) :- mayInferVia(r25,c(patient_point,P,A),l(R)).
inferenceNeeds(c(patient_point,P,A),r25,c(point_weapon_step,R,P)) :- mayInferVia(r25,c(patient_point,P,A),l(R)).
inferenceNeeds(c(patient_point,P,A),r25,c(victim_rob,R,A)) :- mayInferVia(r25,c(patient_point,P,A),l(R)).
comment("instr_point(P,I) <- inst(R,robbing), point_weapon_step(R,P), weapon_rob(R,I)").
mayInferVia(r26,c(instr_point,P,I),l(R)) :- pot(c(instr_point,P,I)), R = s(I,P,27).
numberOfBodies(r26,3).
inferenceNeeds(c(instr_point,P,I),r26,c(inst,R,robbing)) :- mayInferVia(r26,c(instr_point,P,I),l(R)).
inferenceNeeds(c(instr_point,P,I),r26,c(point_weapon_step,R,P)) :- mayInferVia(r26,c(instr_point,P,I),l(R)).
inferenceNeeds(c(instr_point,P,I),r26,c(weapon_rob,R,I)) :- mayInferVia(r26,c(instr_point,P,I),l(R)).
comment("inst(I,weapon) <- inst(R,robbing), weapon_rob(R,I)").
mayInferVia(r27,c(inst,I,weapon),l(R)) :- pot(c(inst,I,weapon)), R = s(I,28).
numberOfBodies(r27,2).
inferenceNeeds(c(inst,I,weapon),r27,c(inst,R,robbing)) :- mayInferVia(r27,c(inst,I,weapon),l(R)).
inferenceNeeds(c(inst,I,weapon),r27,c(weapon_rob,R,I)) :- mayInferVia(r27,c(inst,I,weapon),l(R)).
comment("inst(G,getting) <- inst(R,robbing), get_valuable_step(R,G)").
mayInferVia(r28,c(inst,G,getting),l(R)) :- pot(c(inst,G,getting)), R = s(G,29).
numberOfBodies(r28,2).
inferenceNeeds(c(inst,G,getting),r28,c(inst,R,robbing)) :- mayInferVia(r28,c(inst,G,getting),l(R)).
inferenceNeeds(c(inst,G,getting),r28,c(get_valuable_step,R,G)) :- mayInferVia(r28,c(inst,G,getting),l(R)).
comment("agent_get(G,A) <- inst(R,robbing), get_valuable_step(R,G), robber(R,A)").
mayInferVia(r29,c(agent_get,G,A),l(R)) :- pot(c(agent_get,G,A)), R = s(A,G,30).
numberOfBodies(r29,3).
inferenceNeeds(c(agent_get,G,A),r29,c(inst,R,robbing)) :- mayInferVia(r29,c(agent_get,G,A),l(R)).
inferenceNeeds(c(agent_get,G,A),r29,c(get_valuable_step,R,G)) :- mayInferVia(r29,c(agent_get,G,A),l(R)).
inferenceNeeds(c(agent_get,G,A),r29,c(robber,R,A)) :- mayInferVia(r29,c(agent_get,G,A),l(R)).
comment("patient_get(G,T) <- inst(R,robbing), get_valuable_step(R,G), thing_robbed(R,T)").
mayInferVia(r30,c(patient_get,G,T),l(R)) :- pot(c(patient_get,G,T)), R = s(T,G,31).
numberOfBodies(r30,3).
inferenceNeeds(c(patient_get,G,T),r30,c(inst,R,robbing)) :- mayInferVia(r30,c(patient_get,G,T),l(R)).
inferenceNeeds(c(patient_get,G,T),r30,c(get_valuable_step,R,G)) :- mayInferVia(r30,c(patient_get,G,T),l(R)).
inferenceNeeds(c(patient_get,G,T),r30,c(thing_robbed,R,T)) :- mayInferVia(r30,c(patient_get,G,T),l(R)).
comment("from_get(G,A) <- inst(R,robbing), get_valuable_step(R,G), victim_rob(R,A)").
mayInferVia(r31,c(from_get,G,A),l(R)) :- pot(c(from_get,G,A)), R = s(A,G,32).
numberOfBodies(r31,3).
inferenceNeeds(c(from_get,G,A),r31,c(inst,R,robbing)) :- mayInferVia(r31,c(from_get,G,A),l(R)).
inferenceNeeds(c(from_get,G,A),r31,c(get_valuable_step,R,G)) :- mayInferVia(r31,c(from_get,G,A),l(R)).
inferenceNeeds(c(from_get,G,A),r31,c(victim_rob,R,A)) :- mayInferVia(r31,c(from_get,G,A),l(R)).
comment("inst(T,valuable) <- inst(R,robbing), thing_robbed(R,T)").
mayInferVia(r32,c(inst,T,valuable),l(R)) :- pot(c(inst,T,valuable)), R = s(T,33).
numberOfBodies(r32,2).
inferenceNeeds(c(inst,T,valuable),r32,c(inst,R,robbing)) :- mayInferVia(r32,c(inst,T,valuable),l(R)).
inferenceNeeds(c(inst,T,valuable),r32,c(thing_robbed,R,T)) :- mayInferVia(r32,c(inst,T,valuable),l(R)).
comment("inst(G,going) <- inst(D,rest_dining), go_step(D,G)").
mayInferVia(r33,c(inst,G,going),l(D)) :- pot(c(inst,G,going)), D = s(G,34).
numberOfBodies(r33,2).
inferenceNeeds(c(inst,G,going),r33,c(inst,D,rest_dining)) :- mayInferVia(r33,c(inst,G,going),l(D)).
inferenceNeeds(c(inst,G,going),r33,c(go_step,D,G)) :- mayInferVia(r33,c(inst,G,going),l(D)).
comment("goer(G,A) <- inst(D,rest_dining), go_step(D,G), diner(D,A)").
mayInferVia(r34,c(goer,G,A),l(D)) :- pot(c(goer,G,A)), D = s(A,G,35).
numberOfBodies(r34,3).
inferenceNeeds(c(goer,G,A),r34,c(inst,D,rest_dining)) :- mayInferVia(r34,c(goer,G,A),l(D)).
inferenceNeeds(c(goer,G,A),r34,c(go_step,D,G)) :- mayInferVia(r34,c(goer,G,A),l(D)).
inferenceNeeds(c(goer,G,A),r34,c(diner,D,A)) :- mayInferVia(r34,c(goer,G,A),l(D)).
comment("dest_go(G,R) <- inst(D,rest_dining), go_step(D,G), restaurant(D,R)").
mayInferVia(r35,c(dest_go,G,R),l(D)) :- pot(c(dest_go,G,R)), D = s(R,G,36).
numberOfBodies(r35,3).
inferenceNeeds(c(dest_go,G,R),r35,c(inst,D,rest_dining)) :- mayInferVia(r35,c(dest_go,G,R),l(D)).
inferenceNeeds(c(dest_go,G,R),r35,c(go_step,D,G)) :- mayInferVia(r35,c(dest_go,G,R),l(D)).
inferenceNeeds(c(dest_go,G,R),r35,c(restaurant,D,R)) :- mayInferVia(r35,c(dest_go,G,R),l(D)).
comment("inst(R,restaurant) <- inst(D,rest_dining), restaurant(D,R)").
mayInferVia(r36,c(inst,R,restaurant),l(D)) :- pot(c(inst,R,restaurant)), D = s(R,37).
numberOfBodies(r36,2).
inferenceNeeds(c(inst,R,restaurant),r36,c(inst,D,rest_dining)) :- mayInferVia(r36,c(inst,R,restaurant),l(D)).
inferenceNeeds(c(inst,R,restaurant),r36,c(restaurant,D,R)) :- mayInferVia(r36,c(inst,R,restaurant),l(D)).
comment("inst(O,ordering) <- inst(D,rest_dining), order_step(D,O)").
mayInferVia(r37,c(inst,O,ordering),l(D)) :- pot(c(inst,O,ordering)), D = s(O,38).
numberOfBodies(r37,2).
inferenceNeeds(c(inst,O,ordering),r37,c(inst,D,rest_dining)) :- mayInferVia(r37,c(inst,O,ordering),l(D)).
inferenceNeeds(c(inst,O,ordering),r37,c(order_step,D,O)) :- mayInferVia(r37,c(inst,O,ordering),l(D)).
comment("agent_order(O,A) <- inst(D,rest_dining), order_step(D,O), diner(D,A)").
mayInferVia(r38,c(agent_order,O,A),l(D)) :- pot(c(agent_order,O,A)), D = s(A,O,39).
numberOfBodies(r38,3).
inferenceNeeds(c(agent_order,O,A),r38,c(inst,D,rest_dining)) :- mayInferVia(r38,c(agent_order,O,A),l(D)).
inferenceNeeds(c(agent_order,O,A),r38,c(order_step,D,O)) :- mayInferVia(r38,c(agent_order,O,A),l(D)).
inferenceNeeds(c(agent_order,O,A),r38,c(diner,D,A)) :- mayInferVia(r38,c(agent_order,O,A),l(D)).
comment("patient_order(O,P) <- inst(D,rest_dining), order_step(D,O), rest_thing_ordered(D,P)").
mayInferVia(r39,c(patient_order,O,P),l(D)) :- pot(c(patient_order,O,P)), D = s(P,O,40).
numberOfBodies(r39,3).
inferenceNeeds(c(patient_order,O,P),r39,c(inst,D,rest_dining)) :- mayInferVia(r39,c(patient_order,O,P),l(D)).
inferenceNeeds(c(patient_order,O,P),r39,c(order_step,D,O)) :- mayInferVia(r39,c(patient_order,O,P),l(D)).
inferenceNeeds(c(patient_order,O,P),r39,c(rest_thing_ordered,D,P)) :- mayInferVia(r39,c(patient_order,O,P),l(D)).
comment("inst(O,drinking) <- inst(D,rest_dining), drink_step(D,O)").
mayInferVia(r40,c(inst,O,drinking),l(D)) :- pot(c(inst,O,drinking)), D = s(O,41).
numberOfBodies(r40,2).
inferenceNeeds(c(inst,O,drinking),r40,c(inst,D,rest_dining)) :- mayInferVia(r40,c(inst,O,drinking),l(D)).
inferenceNeeds(c(inst,O,drinking),r40,c(drink_step,D,O)) :- mayInferVia(r40,c(inst,O,drinking),l(D)).
comment("drinker(O,A) <- inst(D,rest_dining), drink_step(D,O), diner(D,A)").
mayInferVia(r41,c(drinker,O,A),l(D)) :- pot(c(drinker,O,A)), D = s(A,O,42).
numberOfBodies(r41,3).
inferenceNeeds(c(drinker,O,A),r41,c(inst,D,rest_dining)) :- mayInferVia(r41,c(drinker,O,A),l(D)).
inferenceNeeds(c(drinker,O,A),r41,c(drink_step,D,O)) :- mayInferVia(r41,c(drinker,O,A),l(D)).
inferenceNeeds(c(drinker,O,A),r41,c(diner,D,A)) :- mayInferVia(r41,c(drinker,O,A),l(D)).
comment("patient_drink(O,P) <- inst(D,rest_dining), drink_step(D,O), rest_thing_drunk(D,P)").
mayInferVia(r42,c(patient_drink,O,P),l(D)) :- pot(c(patient_drink,O,P)), D = s(P,O,43).
numberOfBodies(r42,3).
inferenceNeeds(c(patient_drink,O,P),r42,c(inst,D,rest_dining)) :- mayInferVia(r42,c(patient_drink,O,P),l(D)).
inferenceNeeds(c(patient_drink,O,P),r42,c(drink_step,D,O)) :- mayInferVia(r42,c(patient_drink,O,P),l(D)).
inferenceNeeds(c(patient_drink,O,P),r42,c(rest_thing_drunk,D,P)) :- mayInferVia(r42,c(patient_drink,O,P),l(D)).
comment("instr_drink(O,P) <- inst(D,rest_dining), drink_step(D,O), rest_drink_straw(D,P)").
mayInferVia(r43,c(instr_drink,O,P),l(D)) :- pot(c(instr_drink,O,P)), D = s(P,O,44).
numberOfBodies(r43,3).
inferenceNeeds(c(instr_drink,O,P),r43,c(inst,D,rest_dining)) :- mayInferVia(r43,c(instr_drink,O,P),l(D)).
inferenceNeeds(c(instr_drink,O,P),r43,c(drink_step,D,O)) :- mayInferVia(r43,c(instr_drink,O,P),l(D)).
inferenceNeeds(c(instr_drink,O,P),r43,c(rest_drink_straw,D,P)) :- mayInferVia(r43,c(instr_drink,O,P),l(D)).
comment("inst(O,paying) <- inst(D,rest_dining), pay_step(D,O)").
mayInferVia(r44,c(inst,O,paying),l(D)) :- pot(c(inst,O,paying)), D = s(O,45).
numberOfBodies(r44,2).
inferenceNeeds(c(inst,O,paying),r44,c(inst,D,rest_dining)) :- mayInferVia(r44,c(inst,O,paying),l(D)).
inferenceNeeds(c(inst,O,paying),r44,c(pay_step,D,O)) :- mayInferVia(r44,c(inst,O,paying),l(D)).
comment("payer(O,A) <- inst(D,rest_dining), pay_step(D,O), diner(D,A)").
mayInferVia(r45,c(payer,O,A),l(D)) :- pot(c(payer,O,A)), D = s(A,O,46).
numberOfBodies(r45,3).
inferenceNeeds(c(payer,O,A),r45,c(inst,D,rest_dining)) :- mayInferVia(r45,c(payer,O,A),l(D)).
inferenceNeeds(c(payer,O,A),r45,c(pay_step,D,O)) :- mayInferVia(r45,c(payer,O,A),l(D)).
inferenceNeeds(c(payer,O,A),r45,c(diner,D,A)) :- mayInferVia(r45,c(payer,O,A),l(D)).
comment("thing_paid(O,P) <- inst(D,rest_dining), pay_step(D,O), rest_thing_ordered(D,P)").
mayInferVia(r46,c(thing_paid,O,P),l(D)) :- pot(c(thing_paid,O,P)), D = s(P,O,47).
numberOfBodies(r46,3).
inferenceNeeds(c(thing_paid,O,P),r46,c(inst,D,rest_dining)) :- mayInferVia(r46,c(thing_paid,O,P),l(D)).
inferenceNeeds(c(thing_paid,O,P),r46,c(pay_step,D,O)) :- mayInferVia(r46,c(thing_paid,O,P),l(D)).
inferenceNeeds(c(thing_paid,O,P),r46,c(rest_thing_ordered,D,P)) :- mayInferVia(r46,c(thing_paid,O,P),l(D)).
comment("inst(G,getting) <- inst(D,drinking), get_straw_step(D,G)").
mayInferVia(r47,c(inst,G,getting),l(D)) :- pot(c(inst,G,getting)), D = s(G,48).
numberOfBodies(r47,2).
inferenceNeeds(c(inst,G,getting),r47,c(inst,D,drinking)) :- mayInferVia(r47,c(inst,G,getting),l(D)).
inferenceNeeds(c(inst,G,getting),r47,c(get_straw_step,D,G)) :- mayInferVia(r47,c(inst,G,getting),l(D)).
comment("agent_get(G,A) <- inst(D,drinking), get_straw_step(D,G), drinker(D,A)").
mayInferVia(r48,c(agent_get,G,A),l(D)) :- pot(c(agent_get,G,A)), D = s(A,G,49).
numberOfBodies(r48,3).
inferenceNeeds(c(agent_get,G,A),r48,c(inst,D,drinking)) :- mayInferVia(r48,c(agent_get,G,A),l(D)).
inferenceNeeds(c(agent_get,G,A),r48,c(get_straw_step,D,G)) :- mayInferVia(r48,c(agent_get,G,A),l(D)).
inferenceNeeds(c(agent_get,G,A),r48,c(drinker,D,A)) :- mayInferVia(r48,c(agent_get,G,A),l(D)).
comment("patient_get(G,P) <- inst(D,drinking), get_straw_step(D,G), instr_drink(D,P)").
mayInferVia(r49,c(patient_get,G,P),l(D)) :- pot(c(patient_get,G,P)), D = s(P,G,50).
numberOfBodies(r49,3).
inferenceNeeds(c(patient_get,G,P),r49,c(inst,D,drinking)) :- mayInferVia(r49,c(patient_get,G,P),l(D)).
inferenceNeeds(c(patient_get,G,P),r49,c(get_straw_step,D,G)) :- mayInferVia(r49,c(patient_get,G,P),l(D)).
inferenceNeeds(c(patient_get,G,P),r49,c(instr_drink,D,P)) :- mayInferVia(r49,c(patient_get,G,P),l(D)).
comment("inst(P,putting) <- inst(D,drinking), put_straw_step(D,P)").
mayInferVia(r50,c(inst,P,putting),l(D)) :- pot(c(inst,P,putting)), D = s(P,51).
numberOfBodies(r50,2).
inferenceNeeds(c(inst,P,putting),r50,c(inst,D,drinking)) :- mayInferVia(r50,c(inst,P,putting),l(D)).
inferenceNeeds(c(inst,P,putting),r50,c(put_straw_step,D,P)) :- mayInferVia(r50,c(inst,P,putting),l(D)).
comment("agent_put(P,A) <- inst(D,drinking), put_straw_step(D,P), drinker(D,A)").
mayInferVia(r51,c(agent_put,P,A),l(D)) :- pot(c(agent_put,P,A)), D = s(A,P,52).
numberOfBodies(r51,3).
inferenceNeeds(c(agent_put,P,A),r51,c(inst,D,drinking)) :- mayInferVia(r51,c(agent_put,P,A),l(D)).
inferenceNeeds(c(agent_put,P,A),r51,c(put_straw_step,D,P)) :- mayInferVia(r51,c(agent_put,P,A),l(D)).
inferenceNeeds(c(agent_put,P,A),r51,c(drinker,D,A)) :- mayInferVia(r51,c(agent_put,P,A),l(D)).
comment("patient_put(P,A) <- inst(D,drinking), put_straw_step(D,P), instr_drink(D,A)").
mayInferVia(r52,c(patient_put,P,A),l(D)) :- pot(c(patient_put,P,A)), D = s(A,P,53).
numberOfBodies(r52,3).
inferenceNeeds(c(patient_put,P,A),r52,c(inst,D,drinking)) :- mayInferVia(r52,c(patient_put,P,A),l(D)).
inferenceNeeds(c(patient_put,P,A),r52,c(put_straw_step,D,P)) :- mayInferVia(r52,c(patient_put,P,A),l(D)).
inferenceNeeds(c(patient_put,P,A),r52,c(instr_drink,D,A)) :- mayInferVia(r52,c(patient_put,P,A),l(D)).
comment("inst(A,straw) <- inst(D,drinking), instr_drink(D,A)").
mayInferVia(r53,c(inst,A,straw),l(D)) :- pot(c(inst,A,straw)), D = s(A,54).
numberOfBodies(r53,2).
inferenceNeeds(c(inst,A,straw),r53,c(inst,D,drinking)) :- mayInferVia(r53,c(inst,A,straw),l(D)).
inferenceNeeds(c(inst,A,straw),r53,c(instr_drink,D,A)) :- mayInferVia(r53,c(inst,A,straw),l(D)).
comment("place_put(P,A) <- inst(D,drinking), put_straw_step(D,P), patient_drink(D,A)").
mayInferVia(r54,c(place_put,P,A),l(D)) :- pot(c(place_put,P,A)), D = s(A,P,55).
numberOfBodies(r54,3).
inferenceNeeds(c(place_put,P,A),r54,c(inst,D,drinking)) :- mayInferVia(r54,c(place_put,P,A),l(D)).
inferenceNeeds(c(place_put,P,A),r54,c(put_straw_step,D,P)) :- mayInferVia(r54,c(place_put,P,A),l(D)).
inferenceNeeds(c(place_put,P,A),r54,c(patient_drink,D,A)) :- mayInferVia(r54,c(place_put,P,A),l(D)).
comment("inst(I,ingesting) <- inst(D,drinking), ingest_step(D,I)").
mayInferVia(r55,c(inst,I,ingesting),l(D)) :- pot(c(inst,I,ingesting)), D = s(I,56).
numberOfBodies(r55,2).
inferenceNeeds(c(inst,I,ingesting),r55,c(inst,D,drinking)) :- mayInferVia(r55,c(inst,I,ingesting),l(D)).
inferenceNeeds(c(inst,I,ingesting),r55,c(ingest_step,D,I)) :- mayInferVia(r55,c(inst,I,ingesting),l(D)).
comment("agent_ingest(I,A) <- inst(D,drinking), ingest_step(D,I), drinker(D,A)").
mayInferVia(r56,c(agent_ingest,I,A),l(D)) :- pot(c(agent_ingest,I,A)), D = s(I,A,57).
numberOfBodies(r56,3).
inferenceNeeds(c(agent_ingest,I,A),r56,c(inst,D,drinking)) :- mayInferVia(r56,c(agent_ingest,I,A),l(D)).
inferenceNeeds(c(agent_ingest,I,A),r56,c(ingest_step,D,I)) :- mayInferVia(r56,c(agent_ingest,I,A),l(D)).
inferenceNeeds(c(agent_ingest,I,A),r56,c(drinker,D,A)) :- mayInferVia(r56,c(agent_ingest,I,A),l(D)).
comment("patient_ingest(I,P) <- inst(D,drinking), ingest_step(D,I), patient_drink(D,P)").
mayInferVia(r57,c(patient_ingest,I,P),l(D)) :- pot(c(patient_ingest,I,P)), D = s(I,P,58).
numberOfBodies(r57,3).
inferenceNeeds(c(patient_ingest,I,P),r57,c(inst,D,drinking)) :- mayInferVia(r57,c(patient_ingest,I,P),l(D)).
inferenceNeeds(c(patient_ingest,I,P),r57,c(ingest_step,D,I)) :- mayInferVia(r57,c(patient_ingest,I,P),l(D)).
inferenceNeeds(c(patient_ingest,I,P),r57,c(patient_drink,D,P)) :- mayInferVia(r57,c(patient_ingest,I,P),l(D)).
comment("instr_ingest(I,P) <- inst(D,drinking), ingest_step(D,I), instr_drink(D,P)").
mayInferVia(r58,c(instr_ingest,I,P),l(D)) :- pot(c(instr_ingest,I,P)), D = s(I,P,59).
numberOfBodies(r58,3).
inferenceNeeds(c(instr_ingest,I,P),r58,c(inst,D,drinking)) :- mayInferVia(r58,c(instr_ingest,I,P),l(D)).
inferenceNeeds(c(instr_ingest,I,P),r58,c(ingest_step,D,I)) :- mayInferVia(r58,c(instr_ingest,I,P),l(D)).
inferenceNeeds(c(instr_ingest,I,P),r58,c(instr_drink,D,P)) :- mayInferVia(r58,c(instr_ingest,I,P),l(D)).
comment("inst(G,going) <- inst(V,going_by_vehicle), go_step(V,G)").
mayInferVia(r59,c(inst,G,going),l(V)) :- pot(c(inst,G,going)), V = s(G,60).
numberOfBodies(r59,2).
inferenceNeeds(c(inst,G,going),r59,c(inst,V,going_by_vehicle)) :- mayInferVia(r59,c(inst,G,going),l(V)).
inferenceNeeds(c(inst,G,going),r59,c(go_step,V,G)) :- mayInferVia(r59,c(inst,G,going),l(V)).
comment("goer(G,A) <- inst(V,going_by_vehicle), go_step(V,G), goer(V,A)").
mayInferVia(r60,c(goer,G,A),l(V)) :- pot(c(goer,G,A)), allowrecursiveaxioms, V = s(A,G,61).
numberOfBodies(r60,3).
inferenceNeeds(c(goer,G,A),r60,c(inst,V,going_by_vehicle)) :- mayInferVia(r60,c(goer,G,A),l(V)), allowrecursiveaxioms.
inferenceNeeds(c(goer,G,A),r60,c(go_step,V,G)) :- mayInferVia(r60,c(goer,G,A),l(V)), allowrecursiveaxioms.
inferenceNeeds(c(goer,G,A),r60,c(goer,V,A)) :- mayInferVia(r60,c(goer,G,A),l(V)), allowrecursiveaxioms.
comment("dest_go(G,S) <- inst(V,going_by_vehicle), go_step(V,G), source_go(V,S)").
mayInferVia(r61,c(dest_go,G,S),l(V)) :- pot(c(dest_go,G,S)), V = s(S,G,62).
numberOfBodies(r61,3).
inferenceNeeds(c(dest_go,G,S),r61,c(inst,V,going_by_vehicle)) :- mayInferVia(r61,c(dest_go,G,S),l(V)).
inferenceNeeds(c(dest_go,G,S),r61,c(go_step,V,G)) :- mayInferVia(r61,c(dest_go,G,S),l(V)).
inferenceNeeds(c(dest_go,G,S),r61,c(source_go,V,S)) :- mayInferVia(r61,c(dest_go,G,S),l(V)).
comment("inst(O,getting_on) <- inst(V,going_by_vehicle), get_on_step(V,O)").
mayInferVia(r62,c(inst,O,getting_on),l(V)) :- pot(c(inst,O,getting_on)), V = s(O,63).
numberOfBodies(r62,2).
inferenceNeeds(c(inst,O,getting_on),r62,c(inst,V,going_by_vehicle)) :- mayInferVia(r62,c(inst,O,getting_on),l(V)).
inferenceNeeds(c(inst,O,getting_on),r62,c(get_on_step,V,O)) :- mayInferVia(r62,c(inst,O,getting_on),l(V)).
comment("agent_get_on(O,A) <- inst(V,going_by_vehicle), get_on_step(V,O), goer(V,A)").
mayInferVia(r63,c(agent_get_on,O,A),l(V)) :- pot(c(agent_get_on,O,A)), V = s(A,O,64).
numberOfBodies(r63,3).
inferenceNeeds(c(agent_get_on,O,A),r63,c(inst,V,going_by_vehicle)) :- mayInferVia(r63,c(agent_get_on,O,A),l(V)).
inferenceNeeds(c(agent_get_on,O,A),r63,c(get_on_step,V,O)) :- mayInferVia(r63,c(agent_get_on,O,A),l(V)).
inferenceNeeds(c(agent_get_on,O,A),r63,c(goer,V,A)) :- mayInferVia(r63,c(agent_get_on,O,A),l(V)).
comment("patient_get_on(O,W) <- inst(V,going_by_vehicle), get_on_step(V,O), vehicle(V,W)").
mayInferVia(r64,c(patient_get_on,O,W),l(V)) :- pot(c(patient_get_on,O,W)), V = s(W,O,65).
numberOfBodies(r64,3).
inferenceNeeds(c(patient_get_on,O,W),r64,c(inst,V,going_by_vehicle)) :- mayInferVia(r64,c(patient_get_on,O,W),l(V)).
inferenceNeeds(c(patient_get_on,O,W),r64,c(get_on_step,V,O)) :- mayInferVia(r64,c(patient_get_on,O,W),l(V)).
inferenceNeeds(c(patient_get_on,O,W),r64,c(vehicle,V,W)) :- mayInferVia(r64,c(patient_get_on,O,W),l(V)).
comment("place_get_on(O,P) <- inst(V,going_by_vehicle), get_on_step(V,O), source_go(V,P)").
mayInferVia(r65,c(place_get_on,O,P),l(V)) :- pot(c(place_get_on,O,P)), V = s(P,O,66).
numberOfBodies(r65,3).
inferenceNeeds(c(place_get_on,O,P),r65,c(inst,V,going_by_vehicle)) :- mayInferVia(r65,c(place_get_on,O,P),l(V)).
inferenceNeeds(c(place_get_on,O,P),r65,c(get_on_step,V,O)) :- mayInferVia(r65,c(place_get_on,O,P),l(V)).
inferenceNeeds(c(place_get_on,O,P),r65,c(source_go,V,P)) :- mayInferVia(r65,c(place_get_on,O,P),l(V)).
comment("inst(W,vehicle) <- inst(V,going_by_vehicle), vehicle(V,W)").
mayInferVia(r66,c(inst,W,vehicle),l(V)) :- pot(c(inst,W,vehicle)), V = s(W,67).
numberOfBodies(r66,2).
inferenceNeeds(c(inst,W,vehicle),r66,c(inst,V,going_by_vehicle)) :- mayInferVia(r66,c(inst,W,vehicle),l(V)).
inferenceNeeds(c(inst,W,vehicle),r66,c(vehicle,V,W)) :- mayInferVia(r66,c(inst,W,vehicle),l(V)).
comment("inst(S,sitting) <- inst(V,going_by_vehicle), sit_step(V,S)").
mayInferVia(r67,c(inst,S,sitting),l(V)) :- pot(c(inst,S,sitting)), V = s(S,68).
numberOfBodies(r67,2).
inferenceNeeds(c(inst,S,sitting),r67,c(inst,V,going_by_vehicle)) :- mayInferVia(r67,c(inst,S,sitting),l(V)).
inferenceNeeds(c(inst,S,sitting),r67,c(sit_step,V,S)) :- mayInferVia(r67,c(inst,S,sitting),l(V)).
comment("agent_sit(S,A) <- inst(V,going_by_vehicle), sit_step(V,S), goer(V,A)").
mayInferVia(r68,c(agent_sit,S,A),l(V)) :- pot(c(agent_sit,S,A)), V = s(A,S,69).
numberOfBodies(r68,3).
inferenceNeeds(c(agent_sit,S,A),r68,c(inst,V,going_by_vehicle)) :- mayInferVia(r68,c(agent_sit,S,A),l(V)).
inferenceNeeds(c(agent_sit,S,A),r68,c(sit_step,V,S)) :- mayInferVia(r68,c(agent_sit,S,A),l(V)).
inferenceNeeds(c(agent_sit,S,A),r68,c(goer,V,A)) :- mayInferVia(r68,c(agent_sit,S,A),l(V)).
comment("patient_sit(S,P) <- inst(V,going_by_vehicle), sit_step(V,S), vehicle_seat(V,P)").
mayInferVia(r69,c(patient_sit,S,P),l(V)) :- pot(c(patient_sit,S,P)), V = s(P,S,70).
numberOfBodies(r69,3).
inferenceNeeds(c(patient_sit,S,P),r69,c(inst,V,going_by_vehicle)) :- mayInferVia(r69,c(patient_sit,S,P),l(V)).
inferenceNeeds(c(patient_sit,S,P),r69,c(sit_step,V,S)) :- mayInferVia(r69,c(patient_sit,S,P),l(V)).
inferenceNeeds(c(patient_sit,S,P),r69,c(vehicle_seat,V,P)) :- mayInferVia(r69,c(patient_sit,S,P),l(V)).
comment("inst(P,seat) <- inst(V,going_by_vehicle), vehicle_seat(V,P)").
mayInferVia(r70,c(inst,P,seat),l(V)) :- pot(c(inst,P,seat)), V = s(P,71).
numberOfBodies(r70,2).
inferenceNeeds(c(inst,P,seat),r70,c(inst,V,going_by_vehicle)) :- mayInferVia(r70,c(inst,P,seat),l(V)).
inferenceNeeds(c(inst,P,seat),r70,c(vehicle_seat,V,P)) :- mayInferVia(r70,c(inst,P,seat),l(V)).
comment("in(P,W) <- inst(V,going_by_vehicle), vehicle_seat(V,P), vehicle(V,W)").
mayInferVia(r71,c(in,P,W),l(V)) :- pot(c(in,P,W)), V = s(P,W,72).
numberOfBodies(r71,3).
inferenceNeeds(c(in,P,W),r71,c(inst,V,going_by_vehicle)) :- mayInferVia(r71,c(in,P,W),l(V)).
inferenceNeeds(c(in,P,W),r71,c(vehicle_seat,V,P)) :- mayInferVia(r71,c(in,P,W),l(V)).
inferenceNeeds(c(in,P,W),r71,c(vehicle,V,W)) :- mayInferVia(r71,c(in,P,W),l(V)).
comment("inst(O,getting_off) <- inst(V,going_by_vehicle), get_off_step(V,O)").
mayInferVia(r72,c(inst,O,getting_off),l(V)) :- pot(c(inst,O,getting_off)), V = s(O,73).
numberOfBodies(r72,2).
inferenceNeeds(c(inst,O,getting_off),r72,c(inst,V,going_by_vehicle)) :- mayInferVia(r72,c(inst,O,getting_off),l(V)).
inferenceNeeds(c(inst,O,getting_off),r72,c(get_off_step,V,O)) :- mayInferVia(r72,c(inst,O,getting_off),l(V)).
comment("agent_get_off(O,A) <- inst(V,going_by_vehicle), get_off_step(V,O), goer(V,A)").
mayInferVia(r73,c(agent_get_off,O,A),l(V)) :- pot(c(agent_get_off,O,A)), V = s(A,O,74).
numberOfBodies(r73,3).
inferenceNeeds(c(agent_get_off,O,A),r73,c(inst,V,going_by_vehicle)) :- mayInferVia(r73,c(agent_get_off,O,A),l(V)).
inferenceNeeds(c(agent_get_off,O,A),r73,c(get_off_step,V,O)) :- mayInferVia(r73,c(agent_get_off,O,A),l(V)).
inferenceNeeds(c(agent_get_off,O,A),r73,c(goer,V,A)) :- mayInferVia(r73,c(agent_get_off,O,A),l(V)).
comment("patient_get_off(O,W) <- inst(V,going_by_vehicle), get_off_step(V,O), vehicle(V,W)").
mayInferVia(r74,c(patient_get_off,O,W),l(V)) :- pot(c(patient_get_off,O,W)), V = s(W,O,75).
numberOfBodies(r74,3).
inferenceNeeds(c(patient_get_off,O,W),r74,c(inst,V,going_by_vehicle)) :- mayInferVia(r74,c(patient_get_off,O,W),l(V)).
inferenceNeeds(c(patient_get_off,O,W),r74,c(get_off_step,V,O)) :- mayInferVia(r74,c(patient_get_off,O,W),l(V)).
inferenceNeeds(c(patient_get_off,O,W),r74,c(vehicle,V,W)) :- mayInferVia(r74,c(patient_get_off,O,W),l(V)).
comment("place_get_off(O,P) <- inst(V,going_by_vehicle), get_off_step(V,O), dest_go(V,P)").
mayInferVia(r75,c(place_get_off,O,P),l(V)) :- pot(c(place_get_off,O,P)), V = s(P,O,76).
numberOfBodies(r75,3).
inferenceNeeds(c(place_get_off,O,P),r75,c(inst,V,going_by_vehicle)) :- mayInferVia(r75,c(place_get_off,O,P),l(V)).
inferenceNeeds(c(place_get_off,O,P),r75,c(get_off_step,V,O)) :- mayInferVia(r75,c(place_get_off,O,P),l(V)).
inferenceNeeds(c(place_get_off,O,P),r75,c(dest_go,V,P)) :- mayInferVia(r75,c(place_get_off,O,P),l(V)).
comment("inst(V,bus) <- inst(B,going_by_bus), vehicle(B,V)").
mayInferVia(r76,c(inst,V,bus),l(B)) :- pot(c(inst,V,bus)), B = s(V,77).
numberOfBodies(r76,2).
inferenceNeeds(c(inst,V,bus),r76,c(inst,B,going_by_bus)) :- mayInferVia(r76,c(inst,V,bus),l(B)).
inferenceNeeds(c(inst,V,bus),r76,c(vehicle,B,V)) :- mayInferVia(r76,c(inst,V,bus),l(B)).
comment("inst(V,taxi) <- inst(T,going_by_taxi), vehicle(T,V)").
mayInferVia(r77,c(inst,V,taxi),l(T)) :- pot(c(inst,V,taxi)), T = s(V,78).
numberOfBodies(r77,2).
inferenceNeeds(c(inst,V,taxi),r77,c(inst,T,going_by_taxi)) :- mayInferVia(r77,c(inst,V,taxi),l(T)).
inferenceNeeds(c(inst,V,taxi),r77,c(vehicle,T,V)) :- mayInferVia(r77,c(inst,V,taxi),l(T)).
comment("inst(V,plane) <- inst(P,going_by_plane), vehicle(P,V)").
mayInferVia(r78,c(inst,V,plane),l(P)) :- pot(c(inst,V,plane)), P = s(V,79).
numberOfBodies(r78,2).
inferenceNeeds(c(inst,V,plane),r78,c(inst,P,going_by_plane)) :- mayInferVia(r78,c(inst,V,plane),l(P)).
inferenceNeeds(c(inst,V,plane),r78,c(vehicle,P,V)) :- mayInferVia(r78,c(inst,V,plane),l(P)).
comment("inst(S,bus_station) <- inst(V,going_by_bus), source_go(V,S)").
mayInferVia(r79,c(inst,S,bus_station),l(V)) :- pot(c(inst,S,bus_station)), V = s(S,80).
numberOfBodies(r79,2).
inferenceNeeds(c(inst,S,bus_station),r79,c(inst,V,going_by_bus)) :- mayInferVia(r79,c(inst,S,bus_station),l(V)).
inferenceNeeds(c(inst,S,bus_station),r79,c(source_go,V,S)) :- mayInferVia(r79,c(inst,S,bus_station),l(V)).
comment("inst(G,giving) <- inst(B,going_by_bus), give_token_step(B,G)").
mayInferVia(r80,c(inst,G,giving),l(B)) :- pot(c(inst,G,giving)), B = s(G,81).
numberOfBodies(r80,2).
inferenceNeeds(c(inst,G,giving),r80,c(inst,B,going_by_bus)) :- mayInferVia(r80,c(inst,G,giving),l(B)).
inferenceNeeds(c(inst,G,giving),r80,c(give_token_step,B,G)) :- mayInferVia(r80,c(inst,G,giving),l(B)).
comment("giver(G,A) <- inst(B,going_by_bus), give_token_step(B,G), goer(B,A)").
mayInferVia(r81,c(giver,G,A),l(B)) :- pot(c(giver,G,A)), B = s(A,G,82).
numberOfBodies(r81,3).
inferenceNeeds(c(giver,G,A),r81,c(inst,B,going_by_bus)) :- mayInferVia(r81,c(giver,G,A),l(B)).
inferenceNeeds(c(giver,G,A),r81,c(give_token_step,B,G)) :- mayInferVia(r81,c(giver,G,A),l(B)).
inferenceNeeds(c(giver,G,A),r81,c(goer,B,A)) :- mayInferVia(r81,c(giver,G,A),l(B)).
comment("recipient(G,A) <- inst(B,going_by_bus), give_token_step(B,G), bus_driver(B,A)").
mayInferVia(r82,c(recipient,G,A),l(B)) :- pot(c(recipient,G,A)), B = s(A,G,83).
numberOfBodies(r82,3).
inferenceNeeds(c(recipient,G,A),r82,c(inst,B,going_by_bus)) :- mayInferVia(r82,c(recipient,G,A),l(B)).
inferenceNeeds(c(recipient,G,A),r82,c(give_token_step,B,G)) :- mayInferVia(r82,c(recipient,G,A),l(B)).
inferenceNeeds(c(recipient,G,A),r82,c(bus_driver,B,A)) :- mayInferVia(r82,c(recipient,G,A),l(B)).
comment("occupation(A,busdriver) <- inst(B,going_by_bus), bus_driver(B,A)").
mayInferVia(r83,c(occupation,A,busdriver),l(B)) :- pot(c(occupation,A,busdriver)), B = s(A,84).
numberOfBodies(r83,2).
inferenceNeeds(c(occupation,A,busdriver),r83,c(inst,B,going_by_bus)) :- mayInferVia(r83,c(occupation,A,busdriver),l(B)).
inferenceNeeds(c(occupation,A,busdriver),r83,c(bus_driver,B,A)) :- mayInferVia(r83,c(occupation,A,busdriver),l(B)).
comment("thing_given(G,T) <- inst(B,going_by_bus), give_token_step(B,G), token(B,T)").
mayInferVia(r84,c(thing_given,G,T),l(B)) :- pot(c(thing_given,G,T)), B = s(T,G,85).
numberOfBodies(r84,3).
inferenceNeeds(c(thing_given,G,T),r84,c(inst,B,going_by_bus)) :- mayInferVia(r84,c(thing_given,G,T),l(B)).
inferenceNeeds(c(thing_given,G,T),r84,c(give_token_step,B,G)) :- mayInferVia(r84,c(thing_given,G,T),l(B)).
inferenceNeeds(c(thing_given,G,T),r84,c(token,B,T)) :- mayInferVia(r84,c(thing_given,G,T),l(B)).
comment("inst(T,token) <- inst(B,going_by_bus), token(B,T)").
mayInferVia(r85,c(inst,T,token),l(B)) :- pot(c(inst,T,token)), B = s(T,86).
numberOfBodies(r85,2).
inferenceNeeds(c(inst,T,token),r85,c(inst,B,going_by_bus)) :- mayInferVia(r85,c(inst,T,token),l(B)).
inferenceNeeds(c(inst,T,token),r85,c(token,B,T)) :- mayInferVia(r85,c(inst,T,token),l(B)).
comment("inst(P,paying) <- inst(B,going_by_taxi), pay_step(B,P)").
mayInferVia(r86,c(inst,P,paying),l(B)) :- pot(c(inst,P,paying)), B = s(P,87).
numberOfBodies(r86,2).
inferenceNeeds(c(inst,P,paying),r86,c(inst,B,going_by_taxi)) :- mayInferVia(r86,c(inst,P,paying),l(B)).
inferenceNeeds(c(inst,P,paying),r86,c(pay_step,B,P)) :- mayInferVia(r86,c(inst,P,paying),l(B)).
comment("payer(P,A) <- inst(B,going_by_taxi), pay_step(B,P), goer(B,A)").
mayInferVia(r87,c(payer,P,A),l(B)) :- pot(c(payer,P,A)), B = s(A,P,88).
numberOfBodies(r87,3).
inferenceNeeds(c(payer,P,A),r87,c(inst,B,going_by_taxi)) :- mayInferVia(r87,c(payer,P,A),l(B)).
inferenceNeeds(c(payer,P,A),r87,c(pay_step,B,P)) :- mayInferVia(r87,c(payer,P,A),l(B)).
inferenceNeeds(c(payer,P,A),r87,c(goer,B,A)) :- mayInferVia(r87,c(payer,P,A),l(B)).
comment("payee(P,A) <- inst(B,going_by_taxi), pay_step(B,P), taxi_driver(B,A)").
mayInferVia(r88,c(payee,P,A),l(B)) :- pot(c(payee,P,A)), B = s(A,P,89).
numberOfBodies(r88,3).
inferenceNeeds(c(payee,P,A),r88,c(inst,B,going_by_taxi)) :- mayInferVia(r88,c(payee,P,A),l(B)).
inferenceNeeds(c(payee,P,A),r88,c(pay_step,B,P)) :- mayInferVia(r88,c(payee,P,A),l(B)).
inferenceNeeds(c(payee,P,A),r88,c(taxi_driver,B,A)) :- mayInferVia(r88,c(payee,P,A),l(B)).
comment("occupation(A,taxidriver) <- inst(B,going_by_taxi), taxi_driver(B,A)").
mayInferVia(r89,c(occupation,A,taxidriver),l(B)) :- pot(c(occupation,A,taxidriver)), B = s(A,90).
numberOfBodies(r89,2).
inferenceNeeds(c(occupation,A,taxidriver),r89,c(inst,B,going_by_taxi)) :- mayInferVia(r89,c(occupation,A,taxidriver),l(B)).
inferenceNeeds(c(occupation,A,taxidriver),r89,c(taxi_driver,B,A)) :- mayInferVia(r89,c(occupation,A,taxidriver),l(B)).
comment("inst(S,airport) <- inst(V,going_by_plane), source_go(V,S)").
mayInferVia(r90,c(inst,S,airport),l(V)) :- pot(c(inst,S,airport)), V = s(S,91).
numberOfBodies(r90,2).
inferenceNeeds(c(inst,S,airport),r90,c(inst,V,going_by_plane)) :- mayInferVia(r90,c(inst,S,airport),l(V)).
inferenceNeeds(c(inst,S,airport),r90,c(source_go,V,S)) :- mayInferVia(r90,c(inst,S,airport),l(V)).
comment("inst(S,packing) <- inst(P,going_by_plane), pack_step(P,S)").
mayInferVia(r91,c(inst,S,packing),l(P)) :- pot(c(inst,S,packing)), P = s(S,92).
numberOfBodies(r91,2).
inferenceNeeds(c(inst,S,packing),r91,c(inst,P,going_by_plane)) :- mayInferVia(r91,c(inst,S,packing),l(P)).
inferenceNeeds(c(inst,S,packing),r91,c(pack_step,P,S)) :- mayInferVia(r91,c(inst,S,packing),l(P)).
comment("agent_pack(S,A) <- inst(P,going_by_plane), pack_step(P,S), goer(P,A)").
mayInferVia(r92,c(agent_pack,S,A),l(P)) :- pot(c(agent_pack,S,A)), P = s(A,S,93).
numberOfBodies(r92,3).
inferenceNeeds(c(agent_pack,S,A),r92,c(inst,P,going_by_plane)) :- mayInferVia(r92,c(agent_pack,S,A),l(P)).
inferenceNeeds(c(agent_pack,S,A),r92,c(pack_step,P,S)) :- mayInferVia(r92,c(agent_pack,S,A),l(P)).
inferenceNeeds(c(agent_pack,S,A),r92,c(goer,P,A)) :- mayInferVia(r92,c(agent_pack,S,A),l(P)).
comment("patient_pack(S,L) <- inst(P,going_by_plane), pack_step(P,S), plane_luggage(P,L)").
mayInferVia(r93,c(patient_pack,S,L),l(P)) :- pot(c(patient_pack,S,L)), P = s(S,L,94).
numberOfBodies(r93,3).
inferenceNeeds(c(patient_pack,S,L),r93,c(inst,P,going_by_plane)) :- mayInferVia(r93,c(patient_pack,S,L),l(P)).
inferenceNeeds(c(patient_pack,S,L),r93,c(pack_step,P,S)) :- mayInferVia(r93,c(patient_pack,S,L),l(P)).
inferenceNeeds(c(patient_pack,S,L),r93,c(plane_luggage,P,L)) :- mayInferVia(r93,c(patient_pack,S,L),l(P)).
comment("inst(L,bag) <- inst(P,going_by_plane), plane_luggage(P,L)").
mayInferVia(r94,c(inst,L,bag),l(P)) :- pot(c(inst,L,bag)), P = s(L,95).
numberOfBodies(r94,2).
inferenceNeeds(c(inst,L,bag),r94,c(inst,P,going_by_plane)) :- mayInferVia(r94,c(inst,L,bag),l(P)).
inferenceNeeds(c(inst,L,bag),r94,c(plane_luggage,P,L)) :- mayInferVia(r94,c(inst,L,bag),l(P)).
comment("inst(B,buying) <- inst(S,going_by_plane), buy_ticket_step(S,B)").
mayInferVia(r95,c(inst,B,buying),l(S)) :- pot(c(inst,B,buying)), S = s(B,96).
numberOfBodies(r95,2).
inferenceNeeds(c(inst,B,buying),r95,c(inst,S,going_by_plane)) :- mayInferVia(r95,c(inst,B,buying),l(S)).
inferenceNeeds(c(inst,B,buying),r95,c(buy_ticket_step,S,B)) :- mayInferVia(r95,c(inst,B,buying),l(S)).
comment("buyer(B,A) <- inst(S,going_by_plane), buy_ticket_step(S,B), goer(S,A)").
mayInferVia(r96,c(buyer,B,A),l(S)) :- pot(c(buyer,B,A)), S = s(A,B,97).
numberOfBodies(r96,3).
inferenceNeeds(c(buyer,B,A),r96,c(inst,S,going_by_plane)) :- mayInferVia(r96,c(buyer,B,A),l(S)).
inferenceNeeds(c(buyer,B,A),r96,c(buy_ticket_step,S,B)) :- mayInferVia(r96,c(buyer,B,A),l(S)).
inferenceNeeds(c(buyer,B,A),r96,c(goer,S,A)) :- mayInferVia(r96,c(buyer,B,A),l(S)).
comment("thing_bought(B,T) <- inst(S,going_by_plane), buy_ticket_step(S,B), plane_ticket(S,T)").
mayInferVia(r97,c(thing_bought,B,T),l(S)) :- pot(c(thing_bought,B,T)), S = s(B,T,98).
numberOfBodies(r97,3).
inferenceNeeds(c(thing_bought,B,T),r97,c(inst,S,going_by_plane)) :- mayInferVia(r97,c(thing_bought,B,T),l(S)).
inferenceNeeds(c(thing_bought,B,T),r97,c(buy_ticket_step,S,B)) :- mayInferVia(r97,c(thing_bought,B,T),l(S)).
inferenceNeeds(c(thing_bought,B,T),r97,c(plane_ticket,S,T)) :- mayInferVia(r97,c(thing_bought,B,T),l(S)).
comment("inst(T,ticket) <- inst(S,going_by_plane), plane_ticket(S,T)").
mayInferVia(r98,c(inst,T,ticket),l(S)) :- pot(c(inst,T,ticket)), S = s(T,99).
numberOfBodies(r98,2).
inferenceNeeds(c(inst,T,ticket),r98,c(inst,S,going_by_plane)) :- mayInferVia(r98,c(inst,T,ticket),l(S)).
inferenceNeeds(c(inst,T,ticket),r98,c(plane_ticket,S,T)) :- mayInferVia(r98,c(inst,T,ticket),l(S)).
comment("inst(D,drinking) <- inst(J,jogging), drink_step(J,D)").
mayInferVia(r99,c(inst,D,drinking),l(J)) :- pot(c(inst,D,drinking)), J = s(D,100).
numberOfBodies(r99,2).
inferenceNeeds(c(inst,D,drinking),r99,c(inst,J,jogging)) :- mayInferVia(r99,c(inst,D,drinking),l(J)).
inferenceNeeds(c(inst,D,drinking),r99,c(drink_step,J,D)) :- mayInferVia(r99,c(inst,D,drinking),l(J)).
comment("drinker(D,A) <- inst(J,jogging), drink_step(J,D), jogger(J,A)").
mayInferVia(r100,c(drinker,D,A),l(J)) :- pot(c(drinker,D,A)), J = s(A,D,101).
numberOfBodies(r100,3).
inferenceNeeds(c(drinker,D,A),r100,c(inst,J,jogging)) :- mayInferVia(r100,c(drinker,D,A),l(J)).
inferenceNeeds(c(drinker,D,A),r100,c(drink_step,J,D)) :- mayInferVia(r100,c(drinker,D,A),l(J)).
inferenceNeeds(c(drinker,D,A),r100,c(jogger,J,A)) :- mayInferVia(r100,c(drinker,D,A),l(J)).
comment("patient_drink(D,A) <- inst(J,jogging), drink_step(J,D), jog_thing_drunk(J,A)").
mayInferVia(r101,c(patient_drink,D,A),l(J)) :- pot(c(patient_drink,D,A)), J = s(A,D,102).
numberOfBodies(r101,3).
inferenceNeeds(c(patient_drink,D,A),r101,c(inst,J,jogging)) :- mayInferVia(r101,c(patient_drink,D,A),l(J)).
inferenceNeeds(c(patient_drink,D,A),r101,c(drink_step,J,D)) :- mayInferVia(r101,c(patient_drink,D,A),l(J)).
inferenceNeeds(c(patient_drink,D,A),r101,c(jog_thing_drunk,J,A)) :- mayInferVia(r101,c(patient_drink,D,A),l(J)).
comment("instr_drink(D,A) <- inst(J,jogging), drink_step(J,D), jog_drink_straw(J,A)").
mayInferVia(r102,c(instr_drink,D,A),l(J)) :- pot(c(instr_drink,D,A)), J = s(A,D,103).
numberOfBodies(r102,3).
inferenceNeeds(c(instr_drink,D,A),r102,c(inst,J,jogging)) :- mayInferVia(r102,c(instr_drink,D,A),l(J)).
inferenceNeeds(c(instr_drink,D,A),r102,c(drink_step,J,D)) :- mayInferVia(r102,c(instr_drink,D,A),l(J)).
inferenceNeeds(c(instr_drink,D,A),r102,c(jog_drink_straw,J,A)) :- mayInferVia(r102,c(instr_drink,D,A),l(J)).
comment("inst(D,drinking) <- inst(P,partying), drink_step(P,D)").
mayInferVia(r103,c(inst,D,drinking),l(P)) :- pot(c(inst,D,drinking)), P = s(D,104).
numberOfBodies(r103,2).
inferenceNeeds(c(inst,D,drinking),r103,c(inst,P,partying)) :- mayInferVia(r103,c(inst,D,drinking),l(P)).
inferenceNeeds(c(inst,D,drinking),r103,c(drink_step,P,D)) :- mayInferVia(r103,c(inst,D,drinking),l(P)).
comment("drinker(D,A) <- inst(P,partying), drink_step(P,D), agent_party(P,A)").
mayInferVia(r104,c(drinker,D,A),l(P)) :- pot(c(drinker,D,A)), P = s(A,D,105).
numberOfBodies(r104,3).
inferenceNeeds(c(drinker,D,A),r104,c(inst,P,partying)) :- mayInferVia(r104,c(drinker,D,A),l(P)).
inferenceNeeds(c(drinker,D,A),r104,c(drink_step,P,D)) :- mayInferVia(r104,c(drinker,D,A),l(P)).
inferenceNeeds(c(drinker,D,A),r104,c(agent_party,P,A)) :- mayInferVia(r104,c(drinker,D,A),l(P)).
comment("patient_drink(D,A) <- inst(P,partying), drink_step(P,D), party_thing_drunk(P,A)").
mayInferVia(r105,c(patient_drink,D,A),l(P)) :- pot(c(patient_drink,D,A)), P = s(A,D,106).
numberOfBodies(r105,3).
inferenceNeeds(c(patient_drink,D,A),r105,c(inst,P,partying)) :- mayInferVia(r105,c(patient_drink,D,A),l(P)).
inferenceNeeds(c(patient_drink,D,A),r105,c(drink_step,P,D)) :- mayInferVia(r105,c(patient_drink,D,A),l(P)).
inferenceNeeds(c(patient_drink,D,A),r105,c(party_thing_drunk,P,A)) :- mayInferVia(r105,c(patient_drink,D,A),l(P)).
comment("instr_drink(D,A) <- inst(P,partying), drink_step(P,D), party_drink_straw(P,A)").
mayInferVia(r106,c(instr_drink,D,A),l(P)) :- pot(c(instr_drink,D,A)), P = s(A,D,107).
numberOfBodies(r106,3).
inferenceNeeds(c(instr_drink,D,A),r106,c(inst,P,partying)) :- mayInferVia(r106,c(instr_drink,D,A),l(P)).
inferenceNeeds(c(instr_drink,D,A),r106,c(drink_step,P,D)) :- mayInferVia(r106,c(instr_drink,D,A),l(P)).
inferenceNeeds(c(instr_drink,D,A),r106,c(party_drink_straw,P,A)) :- mayInferVia(r106,c(instr_drink,D,A),l(P)).
comment("inst(X,any) <- inst(X,physical)").
mayInferVia(r107,c(inst,X,any),l) :- pot(c(inst,X,any)).
numberOfBodies(r107,1).
inferenceNeeds(c(inst,X,any),r107,c(inst,X,physical)) :- mayInferVia(r107,c(inst,X,any),l).
comment("inst(X,any) <- inst(X,action)").
mayInferVia(r108,c(inst,X,any),l) :- pot(c(inst,X,any)).
numberOfBodies(r108,1).
inferenceNeeds(c(inst,X,any),r108,c(inst,X,action)) :- mayInferVia(r108,c(inst,X,any),l).
comment("inst(X,physical) <- inst(X,apparel)").
mayInferVia(r109,c(inst,X,physical),l) :- pot(c(inst,X,physical)).
numberOfBodies(r109,1).
inferenceNeeds(c(inst,X,physical),r109,c(inst,X,apparel)) :- mayInferVia(r109,c(inst,X,physical),l).
comment("inst(X,physical) <- inst(X,bag)").
mayInferVia(r110,c(inst,X,physical),l) :- pot(c(inst,X,physical)).
numberOfBodies(r110,1).
inferenceNeeds(c(inst,X,physical),r110,c(inst,X,bag)) :- mayInferVia(r110,c(inst,X,physical),l).
comment("inst(X,physical) <- inst(X,food)").
mayInferVia(r111,c(inst,X,physical),l) :- pot(c(inst,X,physical)).
numberOfBodies(r111,1).
inferenceNeeds(c(inst,X,physical),r111,c(inst,X,food)) :- mayInferVia(r111,c(inst,X,physical),l).
comment("inst(X,physical) <- inst(X,gift)").
mayInferVia(r112,c(inst,X,physical),l) :- pot(c(inst,X,physical)).
numberOfBodies(r112,1).
inferenceNeeds(c(inst,X,physical),r112,c(inst,X,gift)) :- mayInferVia(r112,c(inst,X,physical),l).
comment("inst(X,physical) <- inst(X,liquor)").
mayInferVia(r113,c(inst,X,physical),l) :- pot(c(inst,X,physical)).
numberOfBodies(r113,1).
inferenceNeeds(c(inst,X,physical),r113,c(inst,X,liquor)) :- mayInferVia(r113,c(inst,X,physical),l).
comment("inst(X,physical) <- inst(X,place)").
mayInferVia(r114,c(inst,X,physical),l) :- pot(c(inst,X,physical)).
numberOfBodies(r114,1).
inferenceNeeds(c(inst,X,physical),r114,c(inst,X,place)) :- mayInferVia(r114,c(inst,X,physical),l).
comment("inst(X,physical) <- inst(X,seat)").
mayInferVia(r115,c(inst,X,physical),l) :- pot(c(inst,X,physical)).
numberOfBodies(r115,1).
inferenceNeeds(c(inst,X,physical),r115,c(inst,X,seat)) :- mayInferVia(r115,c(inst,X,physical),l).
comment("inst(X,physical) <- inst(X,shelf)").
mayInferVia(r116,c(inst,X,physical),l) :- pot(c(inst,X,physical)).
numberOfBodies(r116,1).
inferenceNeeds(c(inst,X,physical),r116,c(inst,X,shelf)) :- mayInferVia(r116,c(inst,X,physical),l).
comment("inst(X,physical) <- inst(X,straw)").
mayInferVia(r117,c(inst,X,physical),l) :- pot(c(inst,X,physical)).
numberOfBodies(r117,1).
inferenceNeeds(c(inst,X,physical),r117,c(inst,X,straw)) :- mayInferVia(r117,c(inst,X,physical),l).
comment("inst(X,physical) <- inst(X,ticket)").
mayInferVia(r118,c(inst,X,physical),l) :- pot(c(inst,X,physical)).
numberOfBodies(r118,1).
inferenceNeeds(c(inst,X,physical),r118,c(inst,X,ticket)) :- mayInferVia(r118,c(inst,X,physical),l).
comment("inst(X,physical) <- inst(X,token)").
mayInferVia(r119,c(inst,X,physical),l) :- pot(c(inst,X,physical)).
numberOfBodies(r119,1).
inferenceNeeds(c(inst,X,physical),r119,c(inst,X,token)) :- mayInferVia(r119,c(inst,X,physical),l).
comment("inst(X,physical) <- inst(X,valuable)").
mayInferVia(r120,c(inst,X,physical),l) :- pot(c(inst,X,physical)).
numberOfBodies(r120,1).
inferenceNeeds(c(inst,X,physical),r120,c(inst,X,valuable)) :- mayInferVia(r120,c(inst,X,physical),l).
comment("inst(X,physical) <- inst(X,vehicle)").
mayInferVia(r121,c(inst,X,physical),l) :- pot(c(inst,X,physical)).
numberOfBodies(r121,1).
inferenceNeeds(c(inst,X,physical),r121,c(inst,X,vehicle)) :- mayInferVia(r121,c(inst,X,physical),l).
comment("inst(X,physical) <- inst(X,weapon)").
mayInferVia(r122,c(inst,X,physical),l) :- pot(c(inst,X,physical)).
numberOfBodies(r122,1).
inferenceNeeds(c(inst,X,physical),r122,c(inst,X,weapon)) :- mayInferVia(r122,c(inst,X,physical),l).
comment("inst(X,action) <- inst(X,buying)").
mayInferVia(r123,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r123,1).
inferenceNeeds(c(inst,X,action),r123,c(inst,X,buying)) :- mayInferVia(r123,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,courting)").
mayInferVia(r124,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r124,1).
inferenceNeeds(c(inst,X,action),r124,c(inst,X,courting)) :- mayInferVia(r124,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,drinking)").
mayInferVia(r125,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r125,1).
inferenceNeeds(c(inst,X,action),r125,c(inst,X,drinking)) :- mayInferVia(r125,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,finding)").
mayInferVia(r126,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r126,1).
inferenceNeeds(c(inst,X,action),r126,c(inst,X,finding)) :- mayInferVia(r126,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,getting)").
mayInferVia(r127,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r127,1).
inferenceNeeds(c(inst,X,action),r127,c(inst,X,getting)) :- mayInferVia(r127,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,getting_off)").
mayInferVia(r128,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r128,1).
inferenceNeeds(c(inst,X,action),r128,c(inst,X,getting_off)) :- mayInferVia(r128,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,getting_on)").
mayInferVia(r129,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r129,1).
inferenceNeeds(c(inst,X,action),r129,c(inst,X,getting_on)) :- mayInferVia(r129,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,giving)").
mayInferVia(r130,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r130,1).
inferenceNeeds(c(inst,X,action),r130,c(inst,X,giving)) :- mayInferVia(r130,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,going)").
mayInferVia(r131,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r131,1).
inferenceNeeds(c(inst,X,action),r131,c(inst,X,going)) :- mayInferVia(r131,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,ingesting)").
mayInferVia(r132,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r132,1).
inferenceNeeds(c(inst,X,action),r132,c(inst,X,ingesting)) :- mayInferVia(r132,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,jogging)").
mayInferVia(r133,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r133,1).
inferenceNeeds(c(inst,X,action),r133,c(inst,X,jogging)) :- mayInferVia(r133,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,ordering)").
mayInferVia(r134,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r134,1).
inferenceNeeds(c(inst,X,action),r134,c(inst,X,ordering)) :- mayInferVia(r134,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,packing)").
mayInferVia(r135,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r135,1).
inferenceNeeds(c(inst,X,action),r135,c(inst,X,packing)) :- mayInferVia(r135,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,partying)").
mayInferVia(r136,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r136,1).
inferenceNeeds(c(inst,X,action),r136,c(inst,X,partying)) :- mayInferVia(r136,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,paying)").
mayInferVia(r137,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r137,1).
inferenceNeeds(c(inst,X,action),r137,c(inst,X,paying)) :- mayInferVia(r137,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,pointing)").
mayInferVia(r138,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r138,1).
inferenceNeeds(c(inst,X,action),r138,c(inst,X,pointing)) :- mayInferVia(r138,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,putting)").
mayInferVia(r139,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r139,1).
inferenceNeeds(c(inst,X,action),r139,c(inst,X,putting)) :- mayInferVia(r139,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,rest_dining)").
mayInferVia(r140,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r140,1).
inferenceNeeds(c(inst,X,action),r140,c(inst,X,rest_dining)) :- mayInferVia(r140,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,robbing)").
mayInferVia(r141,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r141,1).
inferenceNeeds(c(inst,X,action),r141,c(inst,X,robbing)) :- mayInferVia(r141,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,shopping)").
mayInferVia(r142,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r142,1).
inferenceNeeds(c(inst,X,action),r142,c(inst,X,shopping)) :- mayInferVia(r142,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,sitting)").
mayInferVia(r143,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r143,1).
inferenceNeeds(c(inst,X,action),r143,c(inst,X,sitting)) :- mayInferVia(r143,c(inst,X,action),l).
comment("inst(X,action) <- inst(X,working)").
mayInferVia(r144,c(inst,X,action),l) :- pot(c(inst,X,action)).
numberOfBodies(r144,1).
inferenceNeeds(c(inst,X,action),r144,c(inst,X,working)) :- mayInferVia(r144,c(inst,X,action),l).
comment("inst(X,apparel) <- inst(X,shirt)").
mayInferVia(r145,c(inst,X,apparel),l) :- pot(c(inst,X,apparel)).
numberOfBodies(r145,1).
inferenceNeeds(c(inst,X,apparel),r145,c(inst,X,shirt)) :- mayInferVia(r145,c(inst,X,apparel),l).
comment("inst(X,apparel) <- inst(X,skirt)").
mayInferVia(r146,c(inst,X,apparel),l) :- pot(c(inst,X,apparel)).
numberOfBodies(r146,1).
inferenceNeeds(c(inst,X,apparel),r146,c(inst,X,skirt)) :- mayInferVia(r146,c(inst,X,apparel),l).
comment("inst(X,apparel) <- inst(X,trousers)").
mayInferVia(r147,c(inst,X,apparel),l) :- pot(c(inst,X,apparel)).
numberOfBodies(r147,1).
inferenceNeeds(c(inst,X,apparel),r147,c(inst,X,trousers)) :- mayInferVia(r147,c(inst,X,apparel),l).
comment("inst(X,apparel) <- inst(X,uniform)").
mayInferVia(r148,c(inst,X,apparel),l) :- pot(c(inst,X,apparel)).
numberOfBodies(r148,1).
inferenceNeeds(c(inst,X,apparel),r148,c(inst,X,uniform)) :- mayInferVia(r148,c(inst,X,apparel),l).
comment("inst(X,bag) <- inst(X,suitcase)").
mayInferVia(r149,c(inst,X,bag),l) :- pot(c(inst,X,bag)).
numberOfBodies(r149,1).
inferenceNeeds(c(inst,X,bag),r149,c(inst,X,suitcase)) :- mayInferVia(r149,c(inst,X,bag),l).
comment("inst(X,food) <- inst(X,bread)").
mayInferVia(r150,c(inst,X,food),l) :- pot(c(inst,X,food)).
numberOfBodies(r150,1).
inferenceNeeds(c(inst,X,food),r150,c(inst,X,bread)) :- mayInferVia(r150,c(inst,X,food),l).
comment("inst(X,food) <- inst(X,milk)").
mayInferVia(r151,c(inst,X,food),l) :- pot(c(inst,X,food)).
numberOfBodies(r151,1).
inferenceNeeds(c(inst,X,food),r151,c(inst,X,milk)) :- mayInferVia(r151,c(inst,X,food),l).
comment("inst(X,food) <- inst(X,milkshake)").
mayInferVia(r152,c(inst,X,food),l) :- pot(c(inst,X,food)).
numberOfBodies(r152,1).
inferenceNeeds(c(inst,X,food),r152,c(inst,X,milkshake)) :- mayInferVia(r152,c(inst,X,food),l).
comment("inst(X,gift) <- inst(X,flower)").
mayInferVia(r153,c(inst,X,gift),l) :- pot(c(inst,X,gift)).
numberOfBodies(r153,1).
inferenceNeeds(c(inst,X,gift),r153,c(inst,X,flower)) :- mayInferVia(r153,c(inst,X,gift),l).
comment("inst(X,gift) <- inst(X,jewelry)").
mayInferVia(r154,c(inst,X,gift),l) :- pot(c(inst,X,gift)).
numberOfBodies(r154,1).
inferenceNeeds(c(inst,X,gift),r154,c(inst,X,jewelry)) :- mayInferVia(r154,c(inst,X,gift),l).
comment("inst(X,liquor) <- inst(X,bourbon)").
mayInferVia(r155,c(inst,X,liquor),l) :- pot(c(inst,X,liquor)).
numberOfBodies(r155,1).
inferenceNeeds(c(inst,X,liquor),r155,c(inst,X,bourbon)) :- mayInferVia(r155,c(inst,X,liquor),l).
comment("inst(X,place) <- inst(X,airport)").
mayInferVia(r156,c(inst,X,place),l) :- pot(c(inst,X,place)).
numberOfBodies(r156,1).
inferenceNeeds(c(inst,X,place),r156,c(inst,X,airport)) :- mayInferVia(r156,c(inst,X,place),l).
comment("inst(X,place) <- inst(X,bus_station)").
mayInferVia(r157,c(inst,X,place),l) :- pot(c(inst,X,place)).
numberOfBodies(r157,1).
inferenceNeeds(c(inst,X,place),r157,c(inst,X,bus_station)) :- mayInferVia(r157,c(inst,X,place),l).
comment("inst(X,place) <- inst(X,park)").
mayInferVia(r158,c(inst,X,place),l) :- pot(c(inst,X,place)).
numberOfBodies(r158,1).
inferenceNeeds(c(inst,X,place),r158,c(inst,X,park)) :- mayInferVia(r158,c(inst,X,place),l).
comment("inst(X,place) <- inst(X,prison)").
mayInferVia(r159,c(inst,X,place),l) :- pot(c(inst,X,place)).
numberOfBodies(r159,1).
inferenceNeeds(c(inst,X,place),r159,c(inst,X,prison)) :- mayInferVia(r159,c(inst,X,place),l).
comment("inst(X,place) <- inst(X,restaurant)").
mayInferVia(r160,c(inst,X,place),l) :- pot(c(inst,X,place)).
numberOfBodies(r160,1).
inferenceNeeds(c(inst,X,place),r160,c(inst,X,restaurant)) :- mayInferVia(r160,c(inst,X,place),l).
comment("inst(X,place) <- inst(X,school)").
mayInferVia(r161,c(inst,X,place),l) :- pot(c(inst,X,place)).
numberOfBodies(r161,1).
inferenceNeeds(c(inst,X,place),r161,c(inst,X,school)) :- mayInferVia(r161,c(inst,X,place),l).
comment("inst(X,place) <- inst(X,shopping_place)").
mayInferVia(r162,c(inst,X,place),l) :- pot(c(inst,X,place)).
numberOfBodies(r162,1).
inferenceNeeds(c(inst,X,place),r162,c(inst,X,shopping_place)) :- mayInferVia(r162,c(inst,X,place),l).
comment("inst(X,valuable) <- inst(X,money)").
mayInferVia(r163,c(inst,X,valuable),l) :- pot(c(inst,X,valuable)).
numberOfBodies(r163,1).
inferenceNeeds(c(inst,X,valuable),r163,c(inst,X,money)) :- mayInferVia(r163,c(inst,X,valuable),l).
comment("inst(X,vehicle) <- inst(X,bus)").
mayInferVia(r164,c(inst,X,vehicle),l) :- pot(c(inst,X,vehicle)).
numberOfBodies(r164,1).
inferenceNeeds(c(inst,X,vehicle),r164,c(inst,X,bus)) :- mayInferVia(r164,c(inst,X,vehicle),l).
comment("inst(X,vehicle) <- inst(X,plane)").
mayInferVia(r165,c(inst,X,vehicle),l) :- pot(c(inst,X,vehicle)).
numberOfBodies(r165,1).
inferenceNeeds(c(inst,X,vehicle),r165,c(inst,X,plane)) :- mayInferVia(r165,c(inst,X,vehicle),l).
comment("inst(X,vehicle) <- inst(X,taxi)").
mayInferVia(r166,c(inst,X,vehicle),l) :- pot(c(inst,X,vehicle)).
numberOfBodies(r166,1).
inferenceNeeds(c(inst,X,vehicle),r166,c(inst,X,taxi)) :- mayInferVia(r166,c(inst,X,vehicle),l).
comment("inst(X,weapon) <- inst(X,gun)").
mayInferVia(r167,c(inst,X,weapon),l) :- pot(c(inst,X,weapon)).
numberOfBodies(r167,1).
inferenceNeeds(c(inst,X,weapon),r167,c(inst,X,gun)) :- mayInferVia(r167,c(inst,X,weapon),l).
comment("inst(X,weapon) <- inst(X,knife)").
mayInferVia(r168,c(inst,X,weapon),l) :- pot(c(inst,X,weapon)).
numberOfBodies(r168,1).
inferenceNeeds(c(inst,X,weapon),r168,c(inst,X,knife)) :- mayInferVia(r168,c(inst,X,weapon),l).
comment("inst(X,going) <- inst(X,going_by_vehicle)").
mayInferVia(r169,c(inst,X,going),l) :- pot(c(inst,X,going)).
numberOfBodies(r169,1).
inferenceNeeds(c(inst,X,going),r169,c(inst,X,going_by_vehicle)) :- mayInferVia(r169,c(inst,X,going),l).
comment("inst(X,shopping) <- inst(X,liqst_shopping)").
mayInferVia(r170,c(inst,X,shopping),l) :- pot(c(inst,X,shopping)).
numberOfBodies(r170,1).
inferenceNeeds(c(inst,X,shopping),r170,c(inst,X,liqst_shopping)) :- mayInferVia(r170,c(inst,X,shopping),l).
comment("inst(X,shopping) <- inst(X,smarket_shopping)").
mayInferVia(r171,c(inst,X,shopping),l) :- pot(c(inst,X,shopping)).
numberOfBodies(r171,1).
inferenceNeeds(c(inst,X,shopping),r171,c(inst,X,smarket_shopping)) :- mayInferVia(r171,c(inst,X,shopping),l).
comment("inst(X,shopping_place) <- inst(X,liquor_store)").
mayInferVia(r172,c(inst,X,shopping_place),l) :- pot(c(inst,X,shopping_place)).
numberOfBodies(r172,1).
inferenceNeeds(c(inst,X,shopping_place),r172,c(inst,X,liquor_store)) :- mayInferVia(r172,c(inst,X,shopping_place),l).
comment("inst(X,shopping_place) <- inst(X,smarket)").
mayInferVia(r173,c(inst,X,shopping_place),l) :- pot(c(inst,X,shopping_place)).
numberOfBodies(r173,1).
inferenceNeeds(c(inst,X,shopping_place),r173,c(inst,X,smarket)) :- mayInferVia(r173,c(inst,X,shopping_place),l).
comment("inst(X,going_by_vehicle) <- inst(X,going_by_bus)").
mayInferVia(r174,c(inst,X,going_by_vehicle),l) :- pot(c(inst,X,going_by_vehicle)).
numberOfBodies(r174,1).
inferenceNeeds(c(inst,X,going_by_vehicle),r174,c(inst,X,going_by_bus)) :- mayInferVia(r174,c(inst,X,going_by_vehicle),l).
comment("inst(X,going_by_vehicle) <- inst(X,going_by_plane)").
mayInferVia(r175,c(inst,X,going_by_vehicle),l) :- pot(c(inst,X,going_by_vehicle)).
numberOfBodies(r175,1).
inferenceNeeds(c(inst,X,going_by_vehicle),r175,c(inst,X,going_by_plane)) :- mayInferVia(r175,c(inst,X,going_by_vehicle),l).
comment("inst(X,going_by_vehicle) <- inst(X,going_by_taxi)").
mayInferVia(r176,c(inst,X,going_by_vehicle),l) :- pot(c(inst,X,going_by_vehicle)).
numberOfBodies(r176,1).
inferenceNeeds(c(inst,X,going_by_vehicle),r176,c(inst,X,going_by_taxi)) :- mayInferVia(r176,c(inst,X,going_by_vehicle),l).
comment("inst(X,shopping) <- go_step(X,A0), find_step(X,A1), buy_step(X,A2)").
mayInferVia(r177,c(inst,X,shopping),l(A1,A0,A2)) :- pot(c(inst,X,shopping)), A0 = s(X,108), A1 = s(X,109), A2 = s(X,110).
numberOfBodies(r177,3).
inferenceNeeds(c(inst,X,shopping),r177,c(go_step,X,A0)) :- mayInferVia(r177,c(inst,X,shopping),l(A1,A0,A2)).
inferenceNeeds(c(inst,X,shopping),r177,c(find_step,X,A1)) :- mayInferVia(r177,c(inst,X,shopping),l(A1,A0,A2)).
inferenceNeeds(c(inst,X,shopping),r177,c(buy_step,X,A2)) :- mayInferVia(r177,c(inst,X,shopping),l(A1,A0,A2)).
comment("inst(X,smarket_shopping) <- go_step(X,A0), find_step(X,A1), buy_step(X,A2)").
mayInferVia(r178,c(inst,X,smarket_shopping),l(A1,A0,A2)) :- pot(c(inst,X,smarket_shopping)), A0 = s(X,111), A1 = s(X,112), A2 = s(X,113).
numberOfBodies(r178,3).
inferenceNeeds(c(inst,X,smarket_shopping),r178,c(go_step,X,A0)) :- mayInferVia(r178,c(inst,X,smarket_shopping),l(A1,A0,A2)).
inferenceNeeds(c(inst,X,smarket_shopping),r178,c(find_step,X,A1)) :- mayInferVia(r178,c(inst,X,smarket_shopping),l(A1,A0,A2)).
inferenceNeeds(c(inst,X,smarket_shopping),r178,c(buy_step,X,A2)) :- mayInferVia(r178,c(inst,X,smarket_shopping),l(A1,A0,A2)).
comment("inst(X,liqst_shopping) <- go_step(X,A0), find_step(X,A1), buy_step(X,A2)").
mayInferVia(r179,c(inst,X,liqst_shopping),l(A1,A0,A2)) :- pot(c(inst,X,liqst_shopping)), A0 = s(X,114), A1 = s(X,115), A2 = s(X,116).
numberOfBodies(r179,3).
inferenceNeeds(c(inst,X,liqst_shopping),r179,c(go_step,X,A0)) :- mayInferVia(r179,c(inst,X,liqst_shopping),l(A1,A0,A2)).
inferenceNeeds(c(inst,X,liqst_shopping),r179,c(find_step,X,A1)) :- mayInferVia(r179,c(inst,X,liqst_shopping),l(A1,A0,A2)).
inferenceNeeds(c(inst,X,liqst_shopping),r179,c(buy_step,X,A2)) :- mayInferVia(r179,c(inst,X,liqst_shopping),l(A1,A0,A2)).
comment("inst(X,buying) <- pay_step(X,A0)").
mayInferVia(r180,c(inst,X,buying),l(A0)) :- pot(c(inst,X,buying)), A0 = s(X,117).
numberOfBodies(r180,1).
inferenceNeeds(c(inst,X,buying),r180,c(pay_step,X,A0)) :- mayInferVia(r180,c(inst,X,buying),l(A0)).
comment("inst(X,robbing) <- get_weapon_step(X,A0), go_step(X,A1), point_weapon_step(X,A2), get_valuable_step(X,A3)").
mayInferVia(r181,c(inst,X,robbing),l(A1,A0,A3,A2)) :- pot(c(inst,X,robbing)), A0 = s(X,118), A1 = s(X,119), A2 = s(X,120), A3 = s(X,121).
numberOfBodies(r181,4).
inferenceNeeds(c(inst,X,robbing),r181,c(get_weapon_step,X,A0)) :- mayInferVia(r181,c(inst,X,robbing),l(A1,A0,A3,A2)).
inferenceNeeds(c(inst,X,robbing),r181,c(go_step,X,A1)) :- mayInferVia(r181,c(inst,X,robbing),l(A1,A0,A3,A2)).
inferenceNeeds(c(inst,X,robbing),r181,c(point_weapon_step,X,A2)) :- mayInferVia(r181,c(inst,X,robbing),l(A1,A0,A3,A2)).
inferenceNeeds(c(inst,X,robbing),r181,c(get_valuable_step,X,A3)) :- mayInferVia(r181,c(inst,X,robbing),l(A1,A0,A3,A2)).
comment("inst(X,rest_dining) <- go_step(X,A0), order_step(X,A1), drink_step(X,A2), pay_step(X,A3)").
mayInferVia(r182,c(inst,X,rest_dining),l(A1,A0,A3,A2)) :- pot(c(inst,X,rest_dining)), A0 = s(X,122), A1 = s(X,123), A2 = s(X,124), A3 = s(X,125).
numberOfBodies(r182,4).
inferenceNeeds(c(inst,X,rest_dining),r182,c(go_step,X,A0)) :- mayInferVia(r182,c(inst,X,rest_dining),l(A1,A0,A3,A2)).
inferenceNeeds(c(inst,X,rest_dining),r182,c(order_step,X,A1)) :- mayInferVia(r182,c(inst,X,rest_dining),l(A1,A0,A3,A2)).
inferenceNeeds(c(inst,X,rest_dining),r182,c(drink_step,X,A2)) :- mayInferVia(r182,c(inst,X,rest_dining),l(A1,A0,A3,A2)).
inferenceNeeds(c(inst,X,rest_dining),r182,c(pay_step,X,A3)) :- mayInferVia(r182,c(inst,X,rest_dining),l(A1,A0,A3,A2)).
comment("inst(X,drinking) <- get_straw_step(X,A0), put_straw_step(X,A1), ingest_step(X,A2)").
mayInferVia(r183,c(inst,X,drinking),l(A1,A0,A2)) :- pot(c(inst,X,drinking)), A0 = s(X,126), A1 = s(X,127), A2 = s(X,128).
numberOfBodies(r183,3).
inferenceNeeds(c(inst,X,drinking),r183,c(get_straw_step,X,A0)) :- mayInferVia(r183,c(inst,X,drinking),l(A1,A0,A2)).
inferenceNeeds(c(inst,X,drinking),r183,c(put_straw_step,X,A1)) :- mayInferVia(r183,c(inst,X,drinking),l(A1,A0,A2)).
inferenceNeeds(c(inst,X,drinking),r183,c(ingest_step,X,A2)) :- mayInferVia(r183,c(inst,X,drinking),l(A1,A0,A2)).
comment("inst(X,going_by_vehicle) <- go_step(X,A0), get_on_step(X,A1), sit_step(X,A2), get_off_step(X,A3)").
mayInferVia(r184,c(inst,X,going_by_vehicle),l(A1,A0,A3,A2)) :- pot(c(inst,X,going_by_vehicle)), A0 = s(X,129), A1 = s(X,130), A2 = s(X,131), A3 = s(X,132).
numberOfBodies(r184,4).
inferenceNeeds(c(inst,X,going_by_vehicle),r184,c(go_step,X,A0)) :- mayInferVia(r184,c(inst,X,going_by_vehicle),l(A1,A0,A3,A2)).
inferenceNeeds(c(inst,X,going_by_vehicle),r184,c(get_on_step,X,A1)) :- mayInferVia(r184,c(inst,X,going_by_vehicle),l(A1,A0,A3,A2)).
inferenceNeeds(c(inst,X,going_by_vehicle),r184,c(sit_step,X,A2)) :- mayInferVia(r184,c(inst,X,going_by_vehicle),l(A1,A0,A3,A2)).
inferenceNeeds(c(inst,X,going_by_vehicle),r184,c(get_off_step,X,A3)) :- mayInferVia(r184,c(inst,X,going_by_vehicle),l(A1,A0,A3,A2)).
comment("inst(X,going_by_bus) <- go_step(X,A0), give_token_step(X,A1), get_on_step(X,A2), sit_step(X,A3), get_off_step(X,A4)").
mayInferVia(r185,c(inst,X,going_by_bus),l(A1,A0,A3,A2,A4)) :- pot(c(inst,X,going_by_bus)), A0 = s(X,133), A1 = s(X,134), A2 = s(X,135), A3 = s(X,136), A4 = s(X,137).
numberOfBodies(r185,5).
inferenceNeeds(c(inst,X,going_by_bus),r185,c(go_step,X,A0)) :- mayInferVia(r185,c(inst,X,going_by_bus),l(A1,A0,A3,A2,A4)).
inferenceNeeds(c(inst,X,going_by_bus),r185,c(give_token_step,X,A1)) :- mayInferVia(r185,c(inst,X,going_by_bus),l(A1,A0,A3,A2,A4)).
inferenceNeeds(c(inst,X,going_by_bus),r185,c(get_on_step,X,A2)) :- mayInferVia(r185,c(inst,X,going_by_bus),l(A1,A0,A3,A2,A4)).
inferenceNeeds(c(inst,X,going_by_bus),r185,c(sit_step,X,A3)) :- mayInferVia(r185,c(inst,X,going_by_bus),l(A1,A0,A3,A2,A4)).
inferenceNeeds(c(inst,X,going_by_bus),r185,c(get_off_step,X,A4)) :- mayInferVia(r185,c(inst,X,going_by_bus),l(A1,A0,A3,A2,A4)).
comment("inst(X,going_by_taxi) <- go_step(X,A0), get_on_step(X,A1), sit_step(X,A2), pay_step(X,A3), get_off_step(X,A4)").
mayInferVia(r186,c(inst,X,going_by_taxi),l(A1,A0,A3,A2,A4)) :- pot(c(inst,X,going_by_taxi)), A0 = s(X,138), A1 = s(X,139), A2 = s(X,140), A3 = s(X,141), A4 = s(X,142).
numberOfBodies(r186,5).
inferenceNeeds(c(inst,X,going_by_taxi),r186,c(go_step,X,A0)) :- mayInferVia(r186,c(inst,X,going_by_taxi),l(A1,A0,A3,A2,A4)).
inferenceNeeds(c(inst,X,going_by_taxi),r186,c(get_on_step,X,A1)) :- mayInferVia(r186,c(inst,X,going_by_taxi),l(A1,A0,A3,A2,A4)).
inferenceNeeds(c(inst,X,going_by_taxi),r186,c(sit_step,X,A2)) :- mayInferVia(r186,c(inst,X,going_by_taxi),l(A1,A0,A3,A2,A4)).
inferenceNeeds(c(inst,X,going_by_taxi),r186,c(pay_step,X,A3)) :- mayInferVia(r186,c(inst,X,going_by_taxi),l(A1,A0,A3,A2,A4)).
inferenceNeeds(c(inst,X,going_by_taxi),r186,c(get_off_step,X,A4)) :- mayInferVia(r186,c(inst,X,going_by_taxi),l(A1,A0,A3,A2,A4)).
comment("inst(X,going_by_plane) <- pack_step(X,A0), go_step(X,A1), buy_ticket_step(X,A2), get_on_step(X,A3), sit_step(X,A4), get_off_step(X,A5)").
mayInferVia(r187,c(inst,X,going_by_plane),l(A1,A0,A3,A2,A5,A4)) :- pot(c(inst,X,going_by_plane)), A0 = s(X,143), A1 = s(X,144), A2 = s(X,145), A3 = s(X,146), A4 = s(X,147), A5 = s(X,148).
numberOfBodies(r187,6).
inferenceNeeds(c(inst,X,going_by_plane),r187,c(pack_step,X,A0)) :- mayInferVia(r187,c(inst,X,going_by_plane),l(A1,A0,A3,A2,A5,A4)).
inferenceNeeds(c(inst,X,going_by_plane),r187,c(go_step,X,A1)) :- mayInferVia(r187,c(inst,X,going_by_plane),l(A1,A0,A3,A2,A5,A4)).
inferenceNeeds(c(inst,X,going_by_plane),r187,c(buy_ticket_step,X,A2)) :- mayInferVia(r187,c(inst,X,going_by_plane),l(A1,A0,A3,A2,A5,A4)).
inferenceNeeds(c(inst,X,going_by_plane),r187,c(get_on_step,X,A3)) :- mayInferVia(r187,c(inst,X,going_by_plane),l(A1,A0,A3,A2,A5,A4)).
inferenceNeeds(c(inst,X,going_by_plane),r187,c(sit_step,X,A4)) :- mayInferVia(r187,c(inst,X,going_by_plane),l(A1,A0,A3,A2,A5,A4)).
inferenceNeeds(c(inst,X,going_by_plane),r187,c(get_off_step,X,A5)) :- mayInferVia(r187,c(inst,X,going_by_plane),l(A1,A0,A3,A2,A5,A4)).
comment("inst(X,jogging) <- drink_step(X,A0)").
mayInferVia(r188,c(inst,X,jogging),l(A0)) :- pot(c(inst,X,jogging)), A0 = s(X,149).
numberOfBodies(r188,1).
inferenceNeeds(c(inst,X,jogging),r188,c(drink_step,X,A0)) :- mayInferVia(r188,c(inst,X,jogging),l(A0)).
comment("inst(X,partying) <- drink_step(X,A0)").
mayInferVia(r189,c(inst,X,partying),l(A0)) :- pot(c(inst,X,partying)), A0 = s(X,150).
numberOfBodies(r189,1).
inferenceNeeds(c(inst,X,partying),r189,c(drink_step,X,A0)) :- mayInferVia(r189,c(inst,X,partying),l(A0)).

%
% == kb/global-constraints.lp ==
%

% KB rewriting for global constraints
comment("mode = eq").
comment("<- go_step(E,V1), go_step(E,V2), V1 != V2 ").
:- true(c(go_step,E1,X)), true(c(go_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- goer(E,V1), goer(E,V2), V1 != V2 ").
:- true(c(goer,E1,X)), true(c(goer,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- dest_go(E,V1), dest_go(E,V2), V1 != V2 ").
:- true(c(dest_go,E1,X)), true(c(dest_go,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- source_go(E,V1), source_go(E,V2), V1 != V2 ").
:- true(c(source_go,E1,X)), true(c(source_go,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- vehicle(E,V1), vehicle(E,V2), V1 != V2 ").
:- true(c(vehicle,E1,X)), true(c(vehicle,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- shopper(E,V1), shopper(E,V2), V1 != V2 ").
:- true(c(shopper,E1,X)), true(c(shopper,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- store(E,V1), store(E,V2), V1 != V2 ").
:- true(c(store,E1,X)), true(c(store,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- thing_shopped_for(E,V1), thing_shopped_for(E,V2), V1 != V2 ").
:- true(c(thing_shopped_for,E1,X)), true(c(thing_shopped_for,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- find_step(E,V1), find_step(E,V2), V1 != V2 ").
:- true(c(find_step,E1,X)), true(c(find_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- finder(E,V1), finder(E,V2), V1 != V2 ").
:- true(c(finder,E1,X)), true(c(finder,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- thing_found(E,V1), thing_found(E,V2), V1 != V2 ").
:- true(c(thing_found,E1,X)), true(c(thing_found,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- buy_step(E,V1), buy_step(E,V2), V1 != V2 ").
:- true(c(buy_step,E1,X)), true(c(buy_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- buyer(E,V1), buyer(E,V2), V1 != V2 ").
:- true(c(buyer,E1,X)), true(c(buyer,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- thing_bought(E,V1), thing_bought(E,V2), V1 != V2 ").
:- true(c(thing_bought,E1,X)), true(c(thing_bought,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- pay_step(E,V1), pay_step(E,V2), V1 != V2 ").
:- true(c(pay_step,E1,X)), true(c(pay_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- payer(E,V1), payer(E,V2), V1 != V2 ").
:- true(c(payer,E1,X)), true(c(payer,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- thing_paid(E,V1), thing_paid(E,V2), V1 != V2 ").
:- true(c(thing_paid,E1,X)), true(c(thing_paid,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- get_straw_step(E,V1), get_straw_step(E,V2), V1 != V2 ").
:- true(c(get_straw_step,E1,X)), true(c(get_straw_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- get_weapon_step(E,V1), get_weapon_step(E,V2), V1 != V2 ").
:- true(c(get_weapon_step,E1,X)), true(c(get_weapon_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- get_valuable_step(E,V1), get_valuable_step(E,V2), V1 != V2 ").
:- true(c(get_valuable_step,E1,X)), true(c(get_valuable_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- agent_get(E,V1), agent_get(E,V2), V1 != V2 ").
:- true(c(agent_get,E1,X)), true(c(agent_get,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- patient_get(E,V1), patient_get(E,V2), V1 != V2 ").
:- true(c(patient_get,E1,X)), true(c(patient_get,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- from_get(E,V1), from_get(E,V2), V1 != V2 ").
:- true(c(from_get,E1,X)), true(c(from_get,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- robber(E,V1), robber(E,V2), V1 != V2 ").
:- true(c(robber,E1,X)), true(c(robber,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- weapon_rob(E,V1), weapon_rob(E,V2), V1 != V2 ").
:- true(c(weapon_rob,E1,X)), true(c(weapon_rob,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- place_rob(E,V1), place_rob(E,V2), V1 != V2 ").
:- true(c(place_rob,E1,X)), true(c(place_rob,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- victim_rob(E,V1), victim_rob(E,V2), V1 != V2 ").
:- true(c(victim_rob,E1,X)), true(c(victim_rob,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- thing_robbed(E,V1), thing_robbed(E,V2), V1 != V2 ").
:- true(c(thing_robbed,E1,X)), true(c(thing_robbed,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- point_weapon_step(E,V1), point_weapon_step(E,V2), V1 != V2 ").
:- true(c(point_weapon_step,E1,X)), true(c(point_weapon_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- agent_point(E,V1), agent_point(E,V2), V1 != V2 ").
:- true(c(agent_point,E1,X)), true(c(agent_point,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- patient_point(E,V1), patient_point(E,V2), V1 != V2 ").
:- true(c(patient_point,E1,X)), true(c(patient_point,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- instr_point(E,V1), instr_point(E,V2), V1 != V2 ").
:- true(c(instr_point,E1,X)), true(c(instr_point,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- diner(E,V1), diner(E,V2), V1 != V2 ").
:- true(c(diner,E1,X)), true(c(diner,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- restaurant(E,V1), restaurant(E,V2), V1 != V2 ").
:- true(c(restaurant,E1,X)), true(c(restaurant,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- rest_thing_ordered(E,V1), rest_thing_ordered(E,V2), V1 != V2 ").
:- true(c(rest_thing_ordered,E1,X)), true(c(rest_thing_ordered,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- rest_thing_drunk(E,V1), rest_thing_drunk(E,V2), V1 != V2 ").
:- true(c(rest_thing_drunk,E1,X)), true(c(rest_thing_drunk,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- rest_drink_straw(E,V1), rest_drink_straw(E,V2), V1 != V2 ").
:- true(c(rest_drink_straw,E1,X)), true(c(rest_drink_straw,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- order_step(E,V1), order_step(E,V2), V1 != V2 ").
:- true(c(order_step,E1,X)), true(c(order_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- agent_order(E,V1), agent_order(E,V2), V1 != V2 ").
:- true(c(agent_order,E1,X)), true(c(agent_order,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- patient_order(E,V1), patient_order(E,V2), V1 != V2 ").
:- true(c(patient_order,E1,X)), true(c(patient_order,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- drink_step(E,V1), drink_step(E,V2), V1 != V2 ").
:- true(c(drink_step,E1,X)), true(c(drink_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- drinker(E,V1), drinker(E,V2), V1 != V2 ").
:- true(c(drinker,E1,X)), true(c(drinker,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- patient_drink(E,V1), patient_drink(E,V2), V1 != V2 ").
:- true(c(patient_drink,E1,X)), true(c(patient_drink,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- instr_drink(E,V1), instr_drink(E,V2), V1 != V2 ").
:- true(c(instr_drink,E1,X)), true(c(instr_drink,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- jogger(E,V1), jogger(E,V2), V1 != V2 ").
:- true(c(jogger,E1,X)), true(c(jogger,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- jog_thing_drunk(E,V1), jog_thing_drunk(E,V2), V1 != V2 ").
:- true(c(jog_thing_drunk,E1,X)), true(c(jog_thing_drunk,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- jog_drink_straw(E,V1), jog_drink_straw(E,V2), V1 != V2 ").
:- true(c(jog_drink_straw,E1,X)), true(c(jog_drink_straw,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- agent_party(E,V1), agent_party(E,V2), V1 != V2 ").
:- true(c(agent_party,E1,X)), true(c(agent_party,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- party_thing_drunk(E,V1), party_thing_drunk(E,V2), V1 != V2 ").
:- true(c(party_thing_drunk,E1,X)), true(c(party_thing_drunk,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- party_drink_straw(E,V1), party_drink_straw(E,V2), V1 != V2 ").
:- true(c(party_drink_straw,E1,X)), true(c(party_drink_straw,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- put_straw_step(E,V1), put_straw_step(E,V2), V1 != V2 ").
:- true(c(put_straw_step,E1,X)), true(c(put_straw_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- agent_put(E,V1), agent_put(E,V2), V1 != V2 ").
:- true(c(agent_put,E1,X)), true(c(agent_put,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- patient_put(E,V1), patient_put(E,V2), V1 != V2 ").
:- true(c(patient_put,E1,X)), true(c(patient_put,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- place_put(E,V1), place_put(E,V2), V1 != V2 ").
:- true(c(place_put,E1,X)), true(c(place_put,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- ingest_step(E,V1), ingest_step(E,V2), V1 != V2 ").
:- true(c(ingest_step,E1,X)), true(c(ingest_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- agent_ingest(E,V1), agent_ingest(E,V2), V1 != V2 ").
:- true(c(agent_ingest,E1,X)), true(c(agent_ingest,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- patient_ingest(E,V1), patient_ingest(E,V2), V1 != V2 ").
:- true(c(patient_ingest,E1,X)), true(c(patient_ingest,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- instr_ingest(E,V1), instr_ingest(E,V2), V1 != V2 ").
:- true(c(instr_ingest,E1,X)), true(c(instr_ingest,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- get_on_step(E,V1), get_on_step(E,V2), V1 != V2 ").
:- true(c(get_on_step,E1,X)), true(c(get_on_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- agent_get_on(E,V1), agent_get_on(E,V2), V1 != V2 ").
:- true(c(agent_get_on,E1,X)), true(c(agent_get_on,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- patient_get_on(E,V1), patient_get_on(E,V2), V1 != V2 ").
:- true(c(patient_get_on,E1,X)), true(c(patient_get_on,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- place_get_on(E,V1), place_get_on(E,V2), V1 != V2 ").
:- true(c(place_get_on,E1,X)), true(c(place_get_on,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- sit_step(E,V1), sit_step(E,V2), V1 != V2 ").
:- true(c(sit_step,E1,X)), true(c(sit_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- agent_sit(E,V1), agent_sit(E,V2), V1 != V2 ").
:- true(c(agent_sit,E1,X)), true(c(agent_sit,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- patient_sit(E,V1), patient_sit(E,V2), V1 != V2 ").
:- true(c(patient_sit,E1,X)), true(c(patient_sit,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- vehicle_seat(E,V1), vehicle_seat(E,V2), V1 != V2 ").
:- true(c(vehicle_seat,E1,X)), true(c(vehicle_seat,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- get_off_step(E,V1), get_off_step(E,V2), V1 != V2 ").
:- true(c(get_off_step,E1,X)), true(c(get_off_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- agent_get_off(E,V1), agent_get_off(E,V2), V1 != V2 ").
:- true(c(agent_get_off,E1,X)), true(c(agent_get_off,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- patient_get_off(E,V1), patient_get_off(E,V2), V1 != V2 ").
:- true(c(patient_get_off,E1,X)), true(c(patient_get_off,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- place_get_off(E,V1), place_get_off(E,V2), V1 != V2 ").
:- true(c(place_get_off,E1,X)), true(c(place_get_off,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- give_token_step(E,V1), give_token_step(E,V2), V1 != V2 ").
:- true(c(give_token_step,E1,X)), true(c(give_token_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- giver(E,V1), giver(E,V2), V1 != V2 ").
:- true(c(giver,E1,X)), true(c(giver,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- recipient(E,V1), recipient(E,V2), V1 != V2 ").
:- true(c(recipient,E1,X)), true(c(recipient,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- occupation(E,V1), occupation(E,V2), V1 != V2 ").
:- true(c(occupation,E1,X)), true(c(occupation,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- thing_given(E,V1), thing_given(E,V2), V1 != V2 ").
:- true(c(thing_given,E1,X)), true(c(thing_given,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- token(E,V1), token(E,V2), V1 != V2 ").
:- true(c(token,E1,X)), true(c(token,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- taxi_driver(E,V1), taxi_driver(E,V2), V1 != V2 ").
:- true(c(taxi_driver,E1,X)), true(c(taxi_driver,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- bus_driver(E,V1), bus_driver(E,V2), V1 != V2 ").
:- true(c(bus_driver,E1,X)), true(c(bus_driver,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- pack_step(E,V1), pack_step(E,V2), V1 != V2 ").
:- true(c(pack_step,E1,X)), true(c(pack_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- agent_pack(E,V1), agent_pack(E,V2), V1 != V2 ").
:- true(c(agent_pack,E1,X)), true(c(agent_pack,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- patient_pack(E,V1), patient_pack(E,V2), V1 != V2 ").
:- true(c(patient_pack,E1,X)), true(c(patient_pack,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- plane_luggage(E,V1), plane_luggage(E,V2), V1 != V2 ").
:- true(c(plane_luggage,E1,X)), true(c(plane_luggage,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- buy_ticket_step(E,V1), buy_ticket_step(E,V2), V1 != V2 ").
:- true(c(buy_ticket_step,E1,X)), true(c(buy_ticket_step,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("<- plane_ticket(E,V1), plane_ticket(E,V2), V1 != V2 ").
:- true(c(plane_ticket,E1,X)), true(c(plane_ticket,E2,Y)), eq(E1,E2), X < Y, not eq(X,Y).
comment("mode = eq").
comment("<- go_step(S,G), goer(G,P)").
:- abduce(c(go_step,S,MyG1)), abduce(c(goer,MyG2,P)), eq(MyG1,MyG2).
comment("<- go_step(S,G), dest_go(G,Str)").
:- abduce(c(go_step,S,MyG1)), abduce(c(dest_go,MyG2,Str)), eq(MyG1,MyG2).
comment("<- find_step(S,F), finder(F,A)").
:- abduce(c(find_step,S,MyF1)), abduce(c(finder,MyF2,A)), eq(MyF1,MyF2).
comment("<- find_step(S,F), thing_found(F,Tf)").
:- abduce(c(find_step,S,MyF1)), abduce(c(thing_found,MyF2,Tf)), eq(MyF1,MyF2).
comment("<- buy_step(S,B), buyer(B,P)").
:- abduce(c(buy_step,S,MyB1)), abduce(c(buyer,MyB2,P)), eq(MyB1,MyB2).
comment("<- buy_step(S,B), thing_bought(B,Tb)").
:- abduce(c(buy_step,S,MyB1)), abduce(c(thing_bought,MyB2,Tb)), eq(MyB1,MyB2).
comment("<- pay_step(B,P), payer(P,A)").
:- abduce(c(pay_step,B,MyP1)), abduce(c(payer,MyP2,A)), eq(MyP1,MyP2).
comment("<- pay_step(B,P), payee(P,A)").
:- abduce(c(pay_step,B,MyP1)), abduce(c(payee,MyP2,A)), eq(MyP1,MyP2).
comment("<- pay_step(B,P), thing_paid(P,Tp)").
:- abduce(c(pay_step,B,MyP1)), abduce(c(thing_paid,MyP2,Tp)), eq(MyP1,MyP2).
comment("<- get_weapon_step(R,G), agent_get(G,A)").
:- abduce(c(get_weapon_step,R,MyG1)), abduce(c(agent_get,MyG2,A)), eq(MyG1,MyG2).
comment("<- get_weapon_step(R,G), patient_get(G,W)").
:- abduce(c(get_weapon_step,R,MyG1)), abduce(c(patient_get,MyG2,W)), eq(MyG1,MyG2).
comment("<- point_weapon_step(R,P), agent_point(P,A)").
:- abduce(c(point_weapon_step,R,MyP1)), abduce(c(agent_point,MyP2,A)), eq(MyP1,MyP2).
comment("<- point_weapon_step(R,P), patient_point(P,A)").
:- abduce(c(point_weapon_step,R,MyP1)), abduce(c(patient_point,MyP2,A)), eq(MyP1,MyP2).
comment("<- point_weapon_step(R,P), instr_point(P,I)").
:- abduce(c(point_weapon_step,R,MyP1)), abduce(c(instr_point,MyP2,I)), eq(MyP1,MyP2).
comment("<- get_valuable_step(R,G), agent_get(G,A)").
:- abduce(c(get_valuable_step,R,MyG1)), abduce(c(agent_get,MyG2,A)), eq(MyG1,MyG2).
comment("<- get_valuable_step(R,G), patient_get(G,T)").
:- abduce(c(get_valuable_step,R,MyG1)), abduce(c(patient_get,MyG2,T)), eq(MyG1,MyG2).
comment("<- get_valuable_step(R,G), from_get(G,A)").
:- abduce(c(get_valuable_step,R,MyG1)), abduce(c(from_get,MyG2,A)), eq(MyG1,MyG2).
comment("<- order_step(D,O), agent_order(O,A)").
:- abduce(c(order_step,D,MyO1)), abduce(c(agent_order,MyO2,A)), eq(MyO1,MyO2).
comment("<- order_step(D,O), patient_order(O,P)").
:- abduce(c(order_step,D,MyO1)), abduce(c(patient_order,MyO2,P)), eq(MyO1,MyO2).
comment("<- drink_step(D,O), drinker(O,A)").
:- abduce(c(drink_step,D,MyO1)), abduce(c(drinker,MyO2,A)), eq(MyO1,MyO2).
comment("<- drink_step(D,O), patient_drink(O,P)").
:- abduce(c(drink_step,D,MyO1)), abduce(c(patient_drink,MyO2,P)), eq(MyO1,MyO2).
comment("<- drink_step(D,O), instr_drink(O,P)").
:- abduce(c(drink_step,D,MyO1)), abduce(c(instr_drink,MyO2,P)), eq(MyO1,MyO2).
comment("<- get_straw_step(D,G), agent_get(G,A)").
:- abduce(c(get_straw_step,D,MyG1)), abduce(c(agent_get,MyG2,A)), eq(MyG1,MyG2).
comment("<- get_straw_step(D,G), patient_get(G,P)").
:- abduce(c(get_straw_step,D,MyG1)), abduce(c(patient_get,MyG2,P)), eq(MyG1,MyG2).
comment("<- put_straw_step(D,P), agent_put(P,A)").
:- abduce(c(put_straw_step,D,MyP1)), abduce(c(agent_put,MyP2,A)), eq(MyP1,MyP2).
comment("<- put_straw_step(D,P), patient_put(P,A)").
:- abduce(c(put_straw_step,D,MyP1)), abduce(c(patient_put,MyP2,A)), eq(MyP1,MyP2).
comment("<- put_straw_step(D,P), place_put(P,A)").
:- abduce(c(put_straw_step,D,MyP1)), abduce(c(place_put,MyP2,A)), eq(MyP1,MyP2).
comment("<- ingest_step(D,I), agent_ingest(I,A)").
:- abduce(c(ingest_step,D,MyI1)), abduce(c(agent_ingest,MyI2,A)), eq(MyI1,MyI2).
comment("<- ingest_step(D,I), patient_ingest(I,P)").
:- abduce(c(ingest_step,D,MyI1)), abduce(c(patient_ingest,MyI2,P)), eq(MyI1,MyI2).
comment("<- ingest_step(D,I), instr_ingest(I,P)").
:- abduce(c(ingest_step,D,MyI1)), abduce(c(instr_ingest,MyI2,P)), eq(MyI1,MyI2).
comment("<- get_on_step(V,O), agent_get_on(O,A)").
:- abduce(c(get_on_step,V,MyO1)), abduce(c(agent_get_on,MyO2,A)), eq(MyO1,MyO2).
comment("<- get_on_step(V,O), patient_get_on(O,W)").
:- abduce(c(get_on_step,V,MyO1)), abduce(c(patient_get_on,MyO2,W)), eq(MyO1,MyO2).
comment("<- get_on_step(V,O), place_get_on(O,P)").
:- abduce(c(get_on_step,V,MyO1)), abduce(c(place_get_on,MyO2,P)), eq(MyO1,MyO2).
comment("<- sit_step(V,S), agent_sit(S,A)").
:- abduce(c(sit_step,V,MyS1)), abduce(c(agent_sit,MyS2,A)), eq(MyS1,MyS2).
comment("<- sit_step(V,S), patient_sit(S,P)").
:- abduce(c(sit_step,V,MyS1)), abduce(c(patient_sit,MyS2,P)), eq(MyS1,MyS2).
comment("<- get_off_step(V,O), agent_get_off(O,A)").
:- abduce(c(get_off_step,V,MyO1)), abduce(c(agent_get_off,MyO2,A)), eq(MyO1,MyO2).
comment("<- get_off_step(V,O), patient_get_off(O,W)").
:- abduce(c(get_off_step,V,MyO1)), abduce(c(patient_get_off,MyO2,W)), eq(MyO1,MyO2).
comment("<- get_off_step(V,O), place_get_off(O,P)").
:- abduce(c(get_off_step,V,MyO1)), abduce(c(place_get_off,MyO2,P)), eq(MyO1,MyO2).
comment("<- give_token_step(B,G), giver(G,A)").
:- abduce(c(give_token_step,B,MyG1)), abduce(c(giver,MyG2,A)), eq(MyG1,MyG2).
comment("<- give_token_step(B,G), recipient(G,A)").
:- abduce(c(give_token_step,B,MyG1)), abduce(c(recipient,MyG2,A)), eq(MyG1,MyG2).
comment("<- give_token_step(B,G), thing_given(G,T)").
:- abduce(c(give_token_step,B,MyG1)), abduce(c(thing_given,MyG2,T)), eq(MyG1,MyG2).
comment("<- pack_step(P,S), agent_pack(S,A)").
:- abduce(c(pack_step,P,MyS1)), abduce(c(agent_pack,MyS2,A)), eq(MyS1,MyS2).
comment("<- pack_step(P,S), patient_pack(S,L)").
:- abduce(c(pack_step,P,MyS1)), abduce(c(patient_pack,MyS2,L)), eq(MyS1,MyS2).
comment("<- buy_ticket_step(S,B), buyer(B,A)").
:- abduce(c(buy_ticket_step,S,MyB1)), abduce(c(buyer,MyB2,A)), eq(MyB1,MyB2).
comment("<- buy_ticket_step(S,B), thing_bought(B,T)").
:- abduce(c(buy_ticket_step,S,MyB1)), abduce(c(thing_bought,MyB2,T)), eq(MyB1,MyB2).

