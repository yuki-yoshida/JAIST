# Verification Sample for a leads-to property of OASIS TOSCA
## Memo of CITP(Constructor-based Inductive Theorem Prover)
### goal Command
 `:goal {eq EXPRESSION = true .}`
 - Define the goal to be proved and let it be the current case. 

### ctf Command
 `:ctf {eq LHS = RHS .}`
 - Split the current case into two cases adding "eq LHS = RHS ." to one case and "eq (LHS = RHS) = false ." to another.

### csp Command
 `:csp {eq LHS1 = RHS1 . eq LHS2 = RHS2 . ...}`
 - Split the current case into several cases adding "eq LHS1 = RHS1 .", "eq LHS2 = RHS2 .", and so on.

### init Command
 `:init [LABEL] by { SUBSTITUTION }`
 - Introduce a nonexec LABELed lemma proven by other proof scores. SUBSTITUTION specifies
   how to unify the lemma to the current case. 

### apply Command
 `:apply (rd)`
 - Try to reduce the goal in the current case.
 - When succeeding to reduce, select the next case as current.

### show proof Command
 `show proof`
 - Summarize the proof tree consisting of split cases. Proven cases are shown by ``*'' marks.

## Several CITP Techniques
### Technique (1)
 - Typically a lemma has a form `A implies B`. When using such lemmas to prove a GOAL, we may define the proof goal as `:goal { eq (A1 implies B1) and (A2 implies B2) and ... implies GOAL . }`. This style is not only complicated but also very expensive to execute. Instead, we can introduce each of such lemmas as an equation in one of the following styles.
   1. `ceq B = true if A .`
   2. `ceq A = false if not B .`
   3. `eq (A and B) = A .`

 - Style i. is suitable when the goal has a form `X implies Y` and the lemma is used to claim Y is true.
 - Style ii. is suitable when the goal has a form `X implies Y` and the lemma is used to claim X is false.
 - However, all variables included in the conditional clause should appear in the left hand side clause.
 - Style iii. is not easy to understand but can be used in both cases without concerning appearance of variables.
 
### Technique (2)
 - When a case including an equation `eq pred(sPR) = true .` where sPR is a proof constant of sort SetOfProperty is split into several cases, some of its descendant may include another equation such as `eq sPR = (aPR sPR') .` where aPR is a proof constant of sort Property and sPR' is of sort SetOfProperty. Then, pred(sPR) reduces to true when it is evaluated from outermost whereas it may not reduce to true when evaluated from innermost. The following idiom can be used to avoid depending on the evaluation strategy of the prover.

  ```
  :set(normalize-init,on)
  :init ( ceq B1 = true if not B2 . ) by { B1 <- pred(sPR) ; B2 <- pred(sPR) == true ; }
  :set(normalize-init,off)
  ```

 - `:set(normalize-init,on)` specifies that the substituted terms be normalized (reduced) before substitution. Then, if pred(sPR) reduces to true, both of B1 and B2 reduce to true and so the introduced equation is `ceq true = true if not true .` which has no meaning. Whereas, if pred(sPR) reduces to B1' which is not true, B2 reduces to false and so the introduced equation is `ceq B1' = true if not false .` which makes B1 reduce to true. As the result, B1 reduces to true anyway.

## Preparation of Proof (Domain.cafe)
### Step 0-1: Define `init(S)` and `final(S)`.
 - Among conditions explicitly composing init(S), one referring to no local states of objects and being expected to be an invariant is called a wfs (well-formed state).
 - Define `wfs(S)` as a conjunction of all wfs's.

  ```
  eq wfs(S)
     = wfs-uniqND(S) and wfs-uniqCP(S) and wfs-uniqRQ(S) and wfs-uniqRL(S) and
       wfs-allCPHaveND(S) and wfs-allRQHaveND(S) and 
       wfs-allCPHaveRL(S) and wfs-allRQHaveRL(S) and 
       wfs-allRLHaveCP(S) and wfs-allRLHaveRQ(S) and 
       wfs-allRLHaveSameTypeCPRQ(S) and
       wfs-allRLNotInSameND(S) and
       wfs-allRLHoldLocality(S) and
       wfs-allNDHaveAtMostOneHost(S) .
  eq init(< SetND,SetCP,SetRQ,SetRL,MP >)
     = not (SetND = empND) and (MP = empMsg) and
       wfs(< SetND,SetCP,SetRQ,SetRL,MP >) and
       noNDCycle(< SetND,SetCP,SetRQ,SetRL,MP >) and
       allNDInStates(SetND,initial) and 
       allCPInStates(SetCP,closed) and 
       allRQInStates(SetRQ,unbound) .
  eq final(< SetND,SetCP,SetRQ,SetRL,MP >)
     = allNDInStates(SetND,started) .
  ```

## Preparation of Proof (Proof.cafe)
### Step 0-2: Define `cont(S)`.
 - Define `cont(S)` as follows using the unconditional search predicate.

  ```
  eq cont(S) = (S =(*,1)=>+ SS) .
  ```

### Step 0-3: Define `m(S)`.
 - Define measuring function `m` as the weighted sum of counting local states of all the classes of objects.

  ```
  eq m(< SetND,SetCP,SetRQ,SetRL,MP >)
     = (( (#NodeInStates(initial,SetND)        * 2) + #NodeInStates(created,SetND))
     +  ( (#CapabilityInStates(closed,SetCP)    * 2) + #CapabilityInStates(open,SetCP)))
     +  ( (#RequirementInStates(unbound,SetRQ) * 2) + #RequirementInStates(waiting,SetRQ)) .
  ```
### Step 0-4: Define `inv(S)`.
 - Each of wfs's and invariants is recommended to define as inv-AAA(S) or wfs-BBB(S).
 - Define `inv(S)` as follows using CITP Technique (1) ii.

  ```
  ceq inv(S) = false if not wfs-uniqND(S) .
  ceq inv(S) = false if not wfs-uniqCP(S) .
  ceq inv(S) = false if not wfs-uniqRQ(S) .
  ceq inv(S) = false if not wfs-uniqRL(S) .
  ceq inv(S) = false if not wfs-allCPHaveND(S) .
  ceq inv(S) = false if not wfs-allRQHaveND(S) .
  ceq inv(S) = false if not wfs-allRLHaveCP(S) .
  ceq inv(S) = false if not wfs-allRLHaveRQ(S) .
  ceq inv(S) = false if not wfs-allCPHaveRL(S) .
  ceq inv(S) = false if not wfs-allRQHaveRL(S) .
  ceq inv(S) = false if not wfs-allRLHaveSameTypeCPRQ(S) .
  ceq inv(S) = false if not wfs-allRLNotInSameND(S) .
  ceq inv(S) = false if not wfs-allRLHoldLocality(S) .
  ceq inv(S) = false if not wfs-allNDHaveAtMostOneHost(S) .
  ceq inv(S) = false if not inv-ifNDInitialThenRQUnboundReady(S) .
  ceq inv(S) = false if not inv-ifNDCreatedThenHostedOnRQReady(S) .
  ceq inv(S) = false if not inv-ifNDStartedThenRQReady(S) .
  ceq inv(S) = false if not inv-ifCPClosedThenRQUnbound(S) .
  ceq inv(S) = false if not inv-ifCPOpenThenRQUnboundWaiting(S) .
  ceq inv(S) = false if not inv-HostedOnCPNotOpen(S) .
  ceq inv(S) = false if not inv-HostedOnRQNotWaiting(S) .
  ceq inv(S) = false if not inv-ifConnectsToCPOpenThenRQWaitingOrOpenMsg(S) .
  ceq inv(S) = false if not inv-ifConnectsToCPAvailableThenRQWaitingReadyOrOpenMsg(S) .
  ceq inv(S) = false if not inv-ifConnectsToCPAvailableThenRQReadyOrAvailableMsg(S) .
  ceq inv(S) = false if not inv-ifOpenMsgThenCPActivated(S) .
  ceq inv(S) = false if not inv-ifAvailableMsgThenCPAvailable(S).
  ```
### Step 0-5: Prepare for using the Cyclic Dependency Lemma.
 - Prepare a nonexec lemma which means that `DDS` of a specified initial node never includes other initial nodes for rule R01.

  ```
  ceq [CycleR01 :nonexec]: 
     true = false if someNDInStates(DDSC(node(T:NDType,I:NDID,initial),S:State),initial) .
  ```

 - Prepare a nonexec lemma which means that `DDS` of a specified created node never includes other created nodes for rule R02.

  ```
  ceq [CycleR02 :nonexec]: 
     true = false if someNDInStates(DDSC(node(T:NDType,I:NDID,created),S:State),created) .
  ```

### Step 0-6: Prepare arbitrary constants.

  ```
  ops idND idND' idND1 idND2 idND3 : -> NDIDLt
  ops idCP idCP' idCP1 idCP2 idCP3 : -> CPIDLt
  ops idRQ idRQ' idRQ1 idRQ2 idRQ3 : -> RQIDLt
  ops idRL idRL' idRL1 idRL2 idRL3 : -> RLIDLt
  ops sND sND' sND'' sND''' : -> SetOfNode
  ops sCP sCP' sCP'' sCP''' : -> SetOfCapability
  ops sRQ sRQ' sRQ'' sRQ''' : -> SetOfRequirement
  ops sRL sRL' sRL'' sRL''' : -> SetOfRelationship
  ops tnd tnd' tnd'' tnd''' : -> NDType
  ops trl trl' trl'' trl''' : -> RLType
  ops snd snd' snd'' : -> NDState
  ops scp scp' scp'' : -> CPState
  ops srq srq' srq'' : -> RQState
  op stND : -> SetOfNDState
  op stCP : -> SetOfCPState
  op stRQ : -> SetOfRQState
  ops mp mp' : -> PoolOfMsg
  op msg : -> Msg
  ```

## Proof of Condition (1): `init(S) implies cont(S)` (Proof-initcont.cafe)
### Step 1-0: Define a predicate to be proved.

  ```
  eq initcont(S) = init(S) implies cont(S) .
  ```

 - Also introduce the Initial Cont Lemma which ensures that `cont(S)` holds if `S` include an initial node.

### Step 1-1: Begin with the most general case. 

  ```
  :goal {eq initcont(< sND, sCP, sRQ, sRL, mp >) = true .}
  ```

### Step 1-2: Consider which rule is applied to the global state in the current case. 
 - The first rule is R01.

### Step 1-3: Split the current case into cases which collectively cover the current case and one of which matches to LHS of the current rule.
 - Since LHS of R01 requires at least one initial node, the root case should be split into following four cases:
  - Case 1: When there is no resource => the goal holds because `init(S)` reduces to false.
  - Case 2-1: When at least one initial node => the goal holds because `cont(S)` reduces to true because of the Initial Cont Lemma.
  - Case 2-2: When at least one created node => the goal holds because `init(S)` reduces to false.
  - Case 2-3: When at least one started node => the goal holds because `init(S)` reduces to false.

## Proof of Condition (2): `inv(S) and not final(S) implies cont(SS) or final(SS)` (Proof-contcont.cafe)
### Step 2-0: Define a predicate to be proved.

  ```
  eq ccont(S,SS)
     = inv(S) and not final(S) implies cont(SS) or final(SS) .
  eq contcont(S)
     = not (S =(*,1)=>+ SS if CC suchThat
            not ((CC implies ccont(S,SS)) == true)
     	   { S => SS !! CC ! inv(S) ! final(S) ! cont(SS) ! final(SS) }) .
  ```

 - Also introduce the Initial Cont Lemma which ensures that `cont(S)` holds if `S` include an initial node
 - And also introduce the Created Cont Lemma which ensures that `cont(S)` holds if `S` include a created node.

## Proof of Condition (2) for R01 (Proof-contcont-R01.cafe)
### Step 2-1: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R01 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq contcont(< (node(tnd,idND,initial) sND), sCP, sRQ, sRL, mp >) = true . }
  ```

### Step 2-2: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The root case should be split into following two cases:
  - Case 1: All hostedOn requirements of the initial node are ready => the goal holds because `cont(SS)` reduces to true because of the Created Cont Lemma.
  - Case 2: Not all hostedOn requirements of the initial node are ready => the goal holds because there is no next state.

## Proof of Condition (2) for R02 (Proof-contcont-R02.cafe)
### Step 2-1: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R02 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq contcont(< (node(tnd,idND,created) sND), sCP, sRQ, sRL, mp >) = true . }
  ```

### Step 2-2: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The root case should be split into following two cases:
  - Case 1: All requirements of the created node are ready.
  - Case 2: Not all requirements of the created node are ready => the goal holds because there is no next state.

### Step 2-3: Split the current case into cases where predicate final does or does not hold in the next state.
 - Since the next state includes one started node and so `final(SS)` holds when all of the rest nodes are started, the current case should be split into following two cases:
  - Case 1-1: When all of the other nodes are started => the goal holds because `final(SS)` reduces to true.
  - Case 1-2: When there is an initial node => the goal holds because `cont(SS)` reduces to true because of the Initial Cont Lemma.
  - Case 1-3: When there is a created node => the goal holds because `cont(SS)` reduces to true because of the Created Cont Lemma.

## Proof of Condition (2) for R03 (Proof-contcont-R03.cafe)
### Step 2-1: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R03 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq contcont(< sND, (cap(hostedOn,idCP,closed,idND) sCP), sRQ, sRL, mp >) = true . }
  ```

### Step 2-2: Split the current case for a rule into cases where the condition of the rule does or does not hold.
 - The root case should be split into following two cases:
  - Case 1: The parent node of the closed capability has been created (isCreated).
  - Case 2: The parent node of the closed capability has not been created yet => the goal holds because there is no next state.

### Step 2-3: Split the current case into cases where predicate final does or does not hold in the next state.
 - The next state after applying R03 is not final because we know a closed capability has an initial parent node.

### Step 2-4: Consider which rule can be applied to the next state.
 - Since there is an available hostedOn capability in the next state, the next rule should be R04.

### Step 2-5: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R04 requires a relationship corresponding to the available capability and an unbound requirement corresponding to the relationship, the current case should be split into following cases:
  - Case 1-1: There is no corresponding relationship => the goal holds because `wfs-allCPHaveRL(S)` reduces to false.
  - Case 1-2: There is a corresponding relationship.
    - Case 1-2-1: The relationship is hostedOn.
      - Case 1-2-1-1: There is no corresponding requirement => the goal holds because `wfs-allRLHaveRQ(S)` reduces to false.
      - Case 1-2-1-2: There is a corresponding requirement.
        - Case 1-2-1-2-1: The requirement is hostedOn.
          - Case 1-2-1-2-1-1: The requirement is unbound => the goal holds because `cont(SS)` reduces to true since R04 is available.
          - Case 1-2-1-2-1-2: The requirement is waiting => the goal holds because `inv-ifCPClosedThenRQUnbound(S)` reduces to false.
          - Case 1-2-1-2-1-3: The requirement is ready => the goal holds because `inv-ifCPClosedThenRQUnbound(S)` reduces to false.
        - Case 1-2-1-2-2: The requirement is dependsOn => the goal holds because `wfs-allRLHaveSameTypeCPRQ(S)` reduces to false.
        - Case 1-2-1-2-3: The requirement is connectsTo => the goal holds because `wfs-allRLHaveSameTypeCPRQ(S)` reduces to false.
    - Case 1-2-2: The relationship is dependsOn => the goal holds because `wfs-allRLHaveSameTypeCPRQ(S)` reduces to false.
    - Case 1-2-3: The relationship is connectsTo => the goal holds because `wfs-allRLHaveSameTypeCPRQ(S)` reduces to false.

## Proof of Condition (2) for R04 (Proof-contcont-R04.cafe)
### Step 2-1: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R04 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal {
    eq contcont(< sND, 
                  (cap(hostedOn,idCP,available,idND) sCP),
                  (req(hostedOn,idRQ,unbound,idND')  sRQ),
                  (rel(hostedOn,idRL,idCP,idRQ)      sRL), mp >) = true .
  }
  ```

### Step 2-2: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - Since R04 is unconditional, this step is ignored.

### Step 2-3: Split the current case into cases where predicate final does or does not hold in the next state.
 - The next state after applying R04 is not final because we know an unbound hostedOn requirement has an initial parent node.

### Step 2-4: Consider which rule can be applied to the next state.
 - Since there is a ready hostedOn requirement in the next state, the next rule should be R01.

### Step 2-5: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R01 requires an initial parent node of the ready requirement, the current case should be split into following four cases:
  - Case 1: There is no such parent node. => the goal holds because `wfs-allRQHaveND(S)` reduces to false.
  - Case 2: There is such a parent node
    - Case 2-1: The node is initial => the goal holds because `cont(SS)` reduces to true because of the Initial Cont Lemma.
    - Case 2-2: The node is created => the goal holds because `inv-ifNDCreatedThenHostedOnRQReady(S)` reduces to false.
    - Case 2-2: The node is started => the goal holds because `inv-ifNDStartedThenRQReady(S)` reduces to false.

## Proof of Condition (2) for R05 (Proof-contcont-R05.cafe)
### Step 2-1: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R05 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq contcont(< sND, (cap(dependsOn,idCP,closed,idND) sCP), sRQ, sRL, mp >) = true . }
  ```

### Step 2-7: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the capability has a dangling `node` link, the current case should be split into following two cases:
  - Case 1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
  - Case 2: There is such a node.

### Step 2-2: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following two cases:
  - Case 2-1: The node corresponding to the capability is initial => the goal holds because `cont(SS)` reduces to true because of the Initial Cont Lemma.
  - Case 2-2: The node corresponding to the capability is created => the goal holds because `cont(SS)` reduces to true because of the Created Cont Lemma.
  - Case 2-3: The node corresponding to the capability is started => the goal holds because `cont(SS)` reduces to true because R06 is available to the next state.

## Proof of Condition (2) for R06 (Proof-contcont-R06.cafe)
### Step 2-1: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R06 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq contcont(< sND, (cap(dependsOn,idCP,open,idND) sCP), sRQ, sRL, mp >) = true . }
  ```

### Step 2-7: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the capability has a dangling `node` link, the current case should be split into following two cases:
  - Case 1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
  - Case 2: There is such a node.

### Step 2-2: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following two cases:
  - Case 2-1: The node corresponding to the capability is initial => the goal holds because `cont(SS)` reduces to true because of the Initial Cont Lemma.
  - Case 2-2: The node corresponding to the capability is created => the goal holds because `cont(SS)` reduces to true because of the Created Cont Lemma.
  - Case 2-3: The node corresponding to the capability is started

### Step 2-3: Split the current case into cases where predicate final does or does not hold in the next state.
 - The next state after applying R06 is not final because we know a open dependsOn capability has a waiting requirement whose parent node is not started.

### Step 2-4: Consider which rule can be applied to the next state.
 - Since there is an available dependsOn capability in the next state, the next rule should be R08.

### Step 2-5: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R08 requires a relationship corresponding to the available capability and a waiting requirement corresponding to the relationship, the current case should be split into following cases:
  - Case 2-3-1: There is no corresponding relationship => the goal holds because `wfs-allCPHaveRL(S)` reduces to false.
  - Case 2-3-2: There is a corresponding relationship.
    - Case 2-3-2-1: The corresponding relationship is hostedOn => the goal holds because `wfs-allRLHaveSameTypeCPRQ` reduces to false.
    - Case 2-3-2-2: The corresponding relationship is dependsOn
      - Case 2-3-2-2-1: There is no corresponding requirement => the goal holds because `wfs-allRLHaveRQ(S)(S)` reduces to false.
      - Case 2-3-2-2-2: There is a corresponding requirement.
        - Case 2-3-2-2-2-1: The corresponding requirement is hostedOn => the goal holds because `wfs-allRLHaveSameTypeCPRQ(S)` reduces to false.
        - Case 2-3-2-2-2-2: The corresponding requirement is dependsOn
          - Case 2-3-2-2-2-2-1: The corresponding requirement is unbound.
          - Case 2-3-2-2-2-2-2: The corresponding requirement is waiting => the goal holds because`cont(SS)` reduces to true because R08 is available to the next state.
          - Case 2-3-2-2-2-2-3: The corresponding requirement is ready => the goal holds because `inv-ifCPClosedThenRQUnbound(S)` reduces to false.
        - Case 2-3-2-2-2-3: The corresponding requirement is connectsTo => the goal holds because `wfs-allRLHaveSameTypeCPRQ(S)` reduces to false.
    - Case 2-3-2-3: The corresponding relationship is connectsTo => the goal holds because `wfs-allRLHaveSameTypeCPRQ(S)` reduces to false.

  - Here, Case 2-3-2-2-2-2-1 remains not to be proved where the current global state is

  ```
  < (node(dependsOn,idND,started) sND'), 
    (cap(dependsOn,idCP,open,idND) sCP), 
    (req(dependsOn,idRQ,unbound,idND')), 
    (rel(dependsOn,idRL,idCP,idRQ) sRL'), mp >
  ```

### Step 2-4: Consider which rule can be applied to the next state.
 - Since there is an unbound dependsOn requirement in the next state, the next rule should be R07.

### Step 2-7: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the requirement has a dangling `node` link, the current case should be split into following two cases
  - Case 2-3-2-2-2-2-1-1: There is no such node => the goal holds because `wfs-allRQHaveND(S)` reduces to false.
  - Case 2-3-2-2-2-2-1-2: There is such a node.

### Step 2-6: Split the current case into cases where the condition of the current rule does or does not hold in the next state.
 - The current case should be split into following three cases:
  - Case 2-3-2-2-2-2-1-2-1: The node is initial => the goal holds because `cont(SS)` reduces to true because of the Initial Cont Lemma.
  - Case 2-3-2-2-2-2-1-2-2: The node is created => the goal holds because `cont(SS)` reduces to true because of the Created Cont Lemma.
  - Case 2-3-2-2-2-2-1-2-3: The node is started => the goal holds because `inv-ifNDStartedThenRQReady(S)` reduces to false.

## Proof of Condition (2) for R07 (Proof-contcont-R07.cafe)
### Step 2-1: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R07 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal {
    eq contcont(< sND, 
                  (cap(dependsOn,idCP,scp,idND) sCP), 
                  (req(dependsOn,idRQ,unbound,idND') sRQ), 
                  (rel(dependsOn,idRL,idCP,idRQ) sRL), mp >) = true .
  }
  ```

### Step 2-7: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the requirement has a dangling `node` link, the current case should be split into following two cases:
  - Case 1: There is no such node => the goal holds because `wfs-allRQHaveND(S)` reduces to false.
  - Case 2: There is such a node.

### Step 2-2: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following two cases:
  - Case 2-1: The node corresponding to the requirement is initial => the goal holds because `cont(SS)` reduces to true because of the Initial Cont Lemma.
  - Case 2-2: The node corresponding to the requirement is created => the goal holds because `cont(SS)` reduces to true because of the Created Cont Lemma.
  - Case 2-3: The node corresponding to the requirement is started => the goal holds because There is no next state.

## Proof of Condition (2) for R08 (Proof-contcont-R08.cafe)
### Step 2-1: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R08 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal {
    eq contcont(< sND, 
                  (cap(dependsOn,idCP,available,idND) sCP), 
                  (req(dependsOn,idRQ,waiting,idND')  sRQ), 
                  (rel(dependsOn,idRL,idCP,idRQ)      sRL), mp >) = true .
  }
  ```
  
### Step 2-7: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the requirement has a dangling `node` link, the current case should be split into following two cases:
  - Case 1: There is no such node => the goal holds because `wfs-allRQHaveND(S)` reduces to false.
  - Case 2: There is such a node.

### Step 2-2: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - Since R08 is unconditional, this step is ignored.

### Step 2-3: Split the current case into cases where predicate final does or does not hold in the next state.
 - The next state after applying R08 is not final because we know a waiting dependsOn requirement has an parent node which is not started.

### Step 2-4: Consider which rule can be applied to the next state.
 - Since there is a ready requirement in the next state, the next rule should be R02.

### Step 2-5: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R02 requires a node corresponding to the requirement is created, the current case should be split into following three cases:
  - Case 2-1: The node corresponding to the requirement is initial => the goal holds because `inv-ifNDInitialThenRQUnboundReady(S)` reduces to false.
  - Case 2-2: The node corresponding to the requirement is created => the goal holds because `cont(SS)` reduces to true because R02 is available to the next state.
  - Case 2-3: The node corresponding to the requirement is started => the goal holds because `inv-ifNDStartedThenRQReady(S)` reduces to false.

## Proof of Condition (2) for R09 (Proof-contcont-R09.cafe)
### Step 2-1: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R09 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq contcont(< sND, (cap(connectsTo,idCP,closed,idND) sCP), sRQ, sRL, mp >) = true . }

  ```
  
### Step 2-7: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the capability has a dangling `node` link, the current case should be split into following two cases:
  - Case 1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
  - Case 2: There is such a node.

### Step 2-2: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following two cases:
  - Case 2-1: The node corresponding to the capability is initial => the goal holds because `cont(SS)` reduces to true because of the Initial Cont Lemma.
  - Case 2-2: The node corresponding to the capability is created => the goal holds because `cont(SS)` reduces to true because of the Created Cont Lemma.
  - Case 2-3: The node corresponding to the capability is started => the goal holds because `cont(SS)` reduces to true because R10 is available to the next state.

## Proof of Condition (2) for R10 (Proof-contcont-R10.cafe)
### Step 2-1: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R10 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq contcont(< sND, (cap(connectsTo,idCP,open,idND) sCP), sRQ, sRL, mp >) = true . }
  ```
  
### Step 2-7: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the capability has a dangling `node` link, the current case should be split into following two cases:
  - Case 1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
  - Case 2: There is such a node.

### Step 2-2: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following two cases:
  - Case 2-1: The node corresponding to the capability is initial => the goal holds because `cont(SS)` reduces to true because of the Initial Cont Lemma.
  - Case 2-2: The node corresponding to the capability is created => the goal holds because `cont(SS)` reduces to true because of the Created Cont Lemma.
  - Case 2-3: The node corresponding to the capability is started

### Step 2-3: Split the current case into cases where predicate final does or does not hold in the next state.
 - The next state after applying R10 is not final because we know a open connectsTo capability has a waiting requirement whose parent node is not started.

### Step 2-4: Consider which rule can be applied to the next state.
 - Since there is an available connectsTo capability in the next state, the next rule should be R12.

### Step 2-5: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R12 requires a relationship corresponding to the available capability and a waiting requirement corresponding to the relationship, the current case should be split into following cases:
  - Case 2-3-1: There is no corresponding relationship => the goal holds because `wfs-allCPHaveRL(S)` reduces to false.
  - Case 2-3-2: There is a corresponding relationship.
    - Case 2-3-2-1: The corresponding relationship is hostedOn => the goal holds because `wfs-allRLHaveSameTypeCPRQ` reduces to false.
    - Case 2-3-2-2: The corresponding relationship is dependsOn => the goal holds because `wfs-allRLHaveSameTypeCPRQ(S)` reduces to false.
    - Case 2-3-2-3: The corresponding relationship is connectsTo
      - Case 2-3-2-3-1: There is no corresponding requirement => the goal holds because `wfs-allRLHaveRQ(S)(S)` reduces to false.
      - Case 2-3-2-3-2: There is a corresponding requirement.
        - Case 2-3-2-3-2-1: The corresponding requirement is hostedOn => the goal holds because `wfs-allRLHaveSameTypeCPRQ(S)` reduces to false.
        - Case 2-3-2-3-2-2: The corresponding requirement is dependsOn => the goal holds because `wfs-allRLHaveSameTypeCPRQ(S)` reduces to false.
        - Case 2-3-2-3-2-3: The corresponding requirement is connectsTo
          - Case 2-3-2-3-2-3-1: The corresponding requirement is unbound
          - Case 2-3-2-3-2-3-2: The corresponding requirement is waiting => the goal holds because`cont(SS)` reduces to true because R12 is available to the next state.
          - Case 2-3-2-3-2-3-3: The corresponding requirement is ready => the goal holds because `inv-ifCPClosedThenRQUnbound(S)` reduces to false.

  - Here, Case 2-3-2-3-2-3-1 remains not to be proved where the current global state is
  ```
  < (node(started,idND,snd) sND'),
    (cap(connectsTo,idCP,open,idND) sCP),
    (req(connectsTo,idRQ,unbound,idND') sRQ'),
    (rel(connectsTo,idRL,idCP,idRQ) sRL'), mp >
  ```

### Step 2-4: Consider which rule can be applied to the next state.
 - Since there is an unbound connectsTo requirement in the next state, the next rule should be R11.

### Step 2-7: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the requirement has a dangling `node` link, the current case should be split into following two cases:
  - Case 2-3-2-3-2-3-1-1: There is no such node => the goal holds because `wfs-allRQHaveND(S)` reduces to false.
  - Case 2-3-2-3-2-3-1-2: There is such a node.

### Step 2-6: Split the current case into cases where the condition of the current rule does or does not hold in the next state.
 - The current case should be split into following three cases:
  - Case 2-3-2-3-2-3-1-2-1: The node corresponding to the unbound requirement is initial => the goal holds because `cont(SS)` reduces to true because of the Initial Cont Lemma.
  - Case 2-3-2-3-2-3-1-2-2: The node corresponding to the unbound requirement is created => the goal holds because `cont(SS)` reduces to true because of the Created Cont Lemma.
  - Case 2-3-2-3-2-3-1-2-3: The node corresponding to the unbound requirement is started => the goal holds because `inv-ifNDStartedThenRQReady(S)` reduces to false.

## Proof of Condition (2) for R11 (Proof-contcont-R11.cafe)
### Step 2-1: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R11 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal {
    eq contcont(< sND, sCP,
                  (req(connectsTo,idRQ,unbound,idND) sRQ), 
                  (rel(connectsTo,idRL,idCP,idRQ) sRL), 
                  (opMsg(idCP) mp) >) = true .
  }
  ```
  
### Step 2-7: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the requirement has a dangling `node` link, the current case should be split into following two cases:
  - Case 1: There is no such node => the goal holds because `wfs-allRQHaveND(S)` reduces to false.
  - Case 2: There is such a node.

### Step 2-2: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following two cases:
  - Case 2-1: The node corresponding to the requirement is initial => the goal holds because `cont(SS)` reduces to true because of the Initial Cont Lemma.
  - Case 2-2: The node corresponding to the requirement is created => the goal holds because `cont(SS)` reduces to true because of the Created Cont Lemma.
  - Case 2-3: The node corresponding to the requirement is started => the goal holds because There is no next state.

## Proof of Condition (2) for R12 (Proof-contcont-R12.cafe)
### Step 2-1: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R12 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal {
    eq contcont(< sND, sCP, 
                  (req(connectsTo,idRQ,waiting,idND) sRQ), 
                  (rel(connectsTo,idRL,idCP,idRQ)    sRL),
                  (avMsg(idCP) mp) >) = true .
  }
  ```
  
### Step 2-7: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the requirement has a dangling `node` link, the current case should be split into following two cases:
  - Case 1: There is no such node => the goal holds because `wfs-allRQHaveND(S)` reduces to false.
  - Case 2: There is such a node.

### Step 2-2: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - Since R12 is unconditional, this step is ignored.

### Step 2-3: Split the current case into cases where predicate final does or does not hold in the next state.
 - The next state after applying R12 is not final because we know a waiting connectsTo requirement has an parent node which is not started.

### Step 2-4: Consider which rule can be applied to the next state.
 - Since there is a ready requirement in the next state, the next rule should be R02.

### Step 2-5: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R02 requires a node corresponding to the waiting requirement, the current case should be split into following three cases:
  - Case 2-1: The node corresponding to the requirement is initial => the goal holds because `inv-ifNDInitialThenRQUnboundReady(S)` reduces to false.
  - Case 2-2: The node corresponding to the requirement is created => the goal holds because `cont(SS)` reduces to true because R02 is available to the next state.
  - Case 2-3: The node corresponding to the requirement is started => the goal holds because `inv-ifNDStartedThenRQReady(S)` reduces to false.

## Proof of Condition (3): `inv(S) and not final(S) implies m(S) > m(SS)` (Proof-measure.cafe)
### Step 3-0: Use natural number axioms.
 - Protecting import model NATAXIOM provided by the framework.

### Step 3-1: Define a predicate to be proved.

  ```
  eq mmes(S,SS)
     = inv(S) and not final(S) implies m(S) > m(SS) .
  eq mesmes(S)
     = not (S =(*,1)=>+ SS if CC suchThat
            not ((CC implies mmes(S,SS)) == true)
     	   { S => SS !! CC ! inv(S) ! final(S) ! (m(S) > m(SS)) }) .
  ```
  
## Proof of Condition (3) for R01
### Step 3-2: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R01 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq mesmes(< (node(tnd,idND,initial) sND), sCP, sRQ, sRL, mp >) = true . }
  ```

### Step 3-3: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The root case should be split into following two cases:
  - Case 1: All hostedOn requirements of the initial node are ready => the goal holds because `m(S) > m(SS)` reduces to true.
  - Case 2: Not all hostedOn requirements of the initial node are ready => the goal holds because there is no next state.

## Proof of Condition (3) for R02
### Step 3-2: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R02 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq mesmes(< (node(tnd,idND,created) sND), sCP, sRQ, sRL, mp >) = true . }
  ```

### Step 3-3: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The root case should be split into following two cases:
  - Case 1: All requirements of the created node are ready => the goal holds because `m(S) > m(SS)` reduces to true.
  - Case 2: Not all requirements of the created node are ready => the goal holds because there is no next state.

## Proof of Condition (3) for R03
### Step 3-2: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R03 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq mesmes(< sND, (cap(hostedOn,idCP,closed,idND) sCP), sRQ, sRL, mp >) = true . }
  ```

### Step 3-3: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The root case should be split into following two cases:
  - Case 1: The parent node of the closed capability has been created (isCreated)  => the goal holds because `m(S) > m(SS)` reduces to true.
  - Case 2: The parent node of the closed capability has not been created yet => the goal holds because there is no next state.

## Proof of Condition (3) for R04
### Step 3-2: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R04 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal {
    eq mesmes(< sND, 
                (cap(hostedOn,idCP,available,idND) sCP),
                (req(hostedOn,idRQ,unbound,idND')  sRQ),
                (rel(hostedOn,idRL,idCP,idRQ)      sRL), mp >) = true .
  }
  ```

### Step 3-3: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - Since R04 is unconditional, this step is ignored.
  - Case 1: The goal holds because `m(S) > m(SS)` reduces to true.

## Proof of Condition (3) for R05
### Step 3-2: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R05 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq mesmes(< sND, (cap(dependsOn,idCP,closed,idND) sCP), sRQ, sRL, mp >) = true . }
  ```

### Step 3-3: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The root case should be split into following two cases:
  - Case 1: The parent node of the closed capability has been created (isCreated)  => the goal holds because `m(S) > m(SS)` reduces to true.
  - Case 2: The parent node of the closed capability has not been created yet => the goal holds because there is no next state.

## Proof of Condition (3) for R06
### Step 3-2: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R06 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq mesmes(< sND, (cap(dependsOn,idCP,open,idND) sCP), sRQ, sRL, mp >) = true . }
  ```

### Step 3-3: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following two cases:
  - Case 1: The parent node of the open capability is started => the goal holds because `m(S) > m(SS)` reduces to true.
  - Case 2: The parent node of the open capability is note started => the goal holds because there is no next state.

## Proof of Condition (3) for R07
### Step 3-2: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R07 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal {
    eq mesmes(< sND, 
                (cap(dependsOn,idCP,scp,idND) sCP), 
                (req(dependsOn,idRQ,unbound,idND') sRQ), 
                (rel(dependsOn,idRL,idCP,idRQ) sRL), mp >) = true .
  }
  ```

### Step 3-3: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following two cases:
  - Case 1: The parent node of the requirement is created and the capability is activated => the goal holds because `m(S) > m(SS)` reduces to true.
  - Case 2: The parent node of the requirement is not created or the capability is not activated => the goal holds because there is no next state.

## Proof of Condition (3) for R08
### Step 3-2: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R08 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal {
    eq mesmes(< sND, 
                (cap(dependsOn,idCP,available,idND) sCP), 
                (req(dependsOn,idRQ,waiting,idND')  sRQ), 
                (rel(dependsOn,idRL,idCP,idRQ)      sRL), mp >) = true .
  }
  ```
  
### Step 3-3: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - Since R08 is unconditional, this step is ignored.
  - Case 1: The goal holds because `m(S) > m(SS)` reduces to true.

## Proof of Condition (3) for R09
### Step 3-2: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R09 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq mesmes(< sND, (cap(connectsTo,idCP,closed,idND) sCP), sRQ, sRL, mp >) = true . }

  ```
  
### Step 3-3: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following two cases:
  - Case 1: The parent node of the closed capability has been created (isCreated)  => the goal holds because `m(S) > m(SS)` reduces to true.
  - Case 2: The parent node of the closed capability has not been created yet => the goal holds because there is no next state.

## Proof of Condition (3) for R10
### Step 3-2: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R07 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal {
    eq mesmes(< sND, 
                (cap(dependsOn,idCP,scp,idND) sCP), 
                (req(dependsOn,idRQ,unbound,idND') sRQ), 
                (rel(dependsOn,idRL,idCP,idRQ) sRL), mp >) = true .
  }
  ```

### Step 3-3: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following two cases:
  - Case 1: The parent node of the open capability is started => the goal holds because `m(S) > m(SS)` reduces to true.
  - Case 2: The parent node of the open capability is note started => the goal holds because there is no next state.

## Proof of Condition (3) for R11
### Step 3-2: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R08 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal {
    eq mesmes(< sND, 
                (cap(dependsOn,idCP,available,idND) sCP), 
                (req(dependsOn,idRQ,waiting,idND')  sRQ), 
                (rel(dependsOn,idRL,idCP,idRQ)      sRL), mp >) = true .
  }
  ```
  
### Step 3-3: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following two cases:
  - Case 1: The parent node of the requirement is created => the goal holds because `m(S) > m(SS)` reduces to true.
  - Case 2: The parent node of the requirement is not created => the goal holds because there is no next state.

## Proof of Condition (3) for R12
### Step 3-2: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R09 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq mesmes(< sND, (cap(connectsTo,idCP,closed,idND) sCP), sRQ, sRL, mp >) = true . }

  ```
  
### Step 3-3: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - Since R08 is unconditional, this step is ignored.
  - Case 1: The goal holds because `m(S) > m(SS)` reduces to true.

## Proof of Condition (4)(5): `init(S) implies inv(S) . inv(S) implies inv(SS) .` (Proof-inv.cafe)

  ```
  eq initinv(S:State)
     = init(S) implies invK(S) .
  eq iinv(S:State,SS:State)
     = inv(S) and invK(S) implies invK(SS) .
  eq invinv(S:State)
     = not (S =(*,1)=>+ SS:State if CC:Bool suchThat
            not ((CC implies iinv(S,SS)) == true)
     	   { S => SS !! CC ! inv(S) ! invK(S) ! invK(SS) }) .
  ```

 - Condition (4)(5) are proved for each invariants and `invK` above will be defined as the target invariant.

## Proof of Initial Cont Lemma (Proof-cyclelemma.cafe)
### Step 1-0: Define a predicate to be proved.

  ```
  eq invcont(S) 
    = cont(S) = true
    when inv(S) .
  ```
 - Prove that invcont(S) holds when S includes at least one initial node.

### Step 1-1: Begin with the most general case.

  ```
  :goal { eq invcont(< (node(tnd, idND, initial) sND), sCP, sRQ, sRL, mp >) = true .}
  ```

 - Since node idND is an arbitrary initial node, the CDL assures that DDS of the node does not include any other initial node.

### Step 1-2 Consider which rule can be applied to the next state.
 - Since there is an initial node, the next rule should be R01.

### Step 1-4: Split the current case into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following three cases:
  - Case 1: All hostedOn requirements of the initial node are ready => the goal holds because R01 is applicable and so `cont(S)` reduces to true.
  - Case 2: At least one  hostedOn requirement of the initial node is unbound.
  - Case 3: At least one  hostedOn requirement of the initial node is waiting =>  the goal holds because `inv-HostedOnRQNotWaiting(S)` reduces to false.

### Step 1-2: Consider which rule can be applied to the next state.
 - Since there is an unbound hostedOn requirement, the next rule should be R04.

### Step 1-5: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the requirement has a dangling `rel` link, the current case should be split into following two cases:
   - Case 2-1: There is no corresponding relationship => the goal holds because `wfs-allRQHaveRL(S)` reduces to false.
   - Case 2-2: There is a corresponding relationship.

 - Since the relationship has a dangling `cap` link, the current case should be split into following two cases:
   - Case 2-2-1: There is no corresponding capability => the goal holds because `wfs-allRLHaveCP(S)` reduces to false.
   - Case 2-2-2: There is a corresponding capability.
   
 - The current case should be split into following two cases:
   - Case 2-2-2-1: The node of the capability is the same as of the requirement => the goal holds because `wfs-allRLNotInSameND(S)` reduces to false.
   - Case 2-2-2-2: The node of the capability is different from the node of the requirement.

### Step 1-3: Split the current case into cases which collectively cover the current case and one of which matches to LHS of the current rule.
 - Since LHS of R04 requires a relationship corresponding to the available capability, the current case should be split into following three cases:
  - Case 2-2-2-2-1: The corresponding capability is closed.
  - Case 2-2-2-2-2: The corresponding capability is open => the goal holds because `inv-HostedOnCPNotOpen(S)` reduces to false.
  - Case 2-2-2-2-3: The corresponding capability is available => the goal holds because R04 is applicable and so `cont(S)` reduces to true.

### Step 1-2: Consider which rule can be applied to the next state.
 - Since there is a closed hostedOn capability, the next rule should be R03.

### Step 1-5: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the capability has a dangling `node` link, the current case should be split into following two cases:
   - Case 2-2-2-2-1-1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
   - Case 2-2-2-2-1-2: There is such a node.

### Step 1-4: Split the current case into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following three cases:
   - Case 2-2-2-2-1-2-1: the node of the capability is initial => the goal holds because DDSR01 of the initial node includes another initial node which is a contradiction. 
   - Case 2-2-2-2-1-2-2: the node of the capability is created => the goal holds because R03 is applicable and so `cont(S)` reduces to true.
   - Case 2-2-2-2-1-2-3: the node of the capability is started => the goal holds because R03 is applicable and so `cont(S)` reduces to true.

## Created Cont Lemmaの証明譜(Proof-cyclelemma.cafe)
### Step 1-0: Define a predicate to be proved.
 - Prove that invcont(S) holds when S includes at least one created node.
 - Introduce the Initial Cont Lemma proved above.

  ```
  eq cont(< (node(T, I, initial) SetND), 
             SetCP, SetRQ, SetRL, M >) = true .
  ```

### Step 1-1: Begin with the most general case. 

  ```
  :goal {eq invcont(< (node(tnd, idND, created) sND), sCP, sRQ, sRL, mp >)  = true .}
  ```

 - Since node idND is an arbitrary initial node, the CDL assures that DDS of the node does not include any other created node.

### Step 1-2: Consider which rule can be applied to the global state in the current case. 
 - Since there is a created node, the next rule should be R02.

### Step 1-4: Split the current case into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following three cases:
  - Case 1: All requirements of the created node are ready => the goal holds because R02 is applicable and so `cont(S)` reduces to true.
  - Case 2: One of requirements of the created node is unbound.
  - Case 3: One of requirements of the created node is waiting.

### Case 2: One of requirements of the created node is unbound.
### Step 1-2: Consider which rule can be applied to the global state in the current case. 
 - Since the next applicable rule depends on the type of the unbound requirement, the current case should be split into following three cases:
  - Case 2-1: The type of the unbound requirement is hostedOn => the goal holds because `inv-ifNDCreatedThenHostedOnRQReady(S)` reduces to false.
  - Case 2-2: The type of the unbound requirement is dependsOn.
  - Case 2-3: The type of the unbound requirement is connectsTo.

### Case 2-2: The type of the unbound requirement is dependsOn.
### Step 1-2: Consider which rule can be applied to the global state in the current case. 
 - Since there is an unbound dependsOn requirement, the next rule should be R07.

### Step 1-3: Split the current case into cases which collectively cover the current case and one of which matches to LHS of the current rule.
 - LHS of R07 requires a relationship corresponding to the requiement and a capability corresponding to the relationship.

### Step 1-5: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the requirement has a dangling `rel` link, the current case should be split into following two cases:
   - Case 2-2-1: There is no corresponding relationship => the goal holds because `wfs-allRQHaveRL(S)` reduces to false.
   - Case 2-2-2: There is a corresponding relationship.

 - Since the relationship has a dangling `cap` link, the current case should be split into following two case   - Case 2-2-2-1: There is no corresponding capability => the goal holds because `wfs-allRLHaveCP(S)` reduces to false.
   - Case 2-2-2-2: There is a corresponding capability.
   
 - The current case should be split into following two cases:
   - Case 2-2-2-2-1: The node of the capability is the same as of the requirement => the goal holds because `wfs-allRLNotInSameND(S)` reduces to false.
   - Case 2-2-2-2-2: The node of the capability is different from the node of the requirement.

### Step 1-3: Split the current case into cases which collectively cover the current case and one of which matches to LHS of the current rule.
 - Since LHS of R07 requires an activated capability corresponding to the requirement, the current case should be split into following three cases:
  - Case 2-2-2-2-2-1: The corresponding capability is closed.
  - Case 2-2-2-2-2-2: The corresponding capability is open => the goal holds because R07 is applicable and so `cont(S)` reduces to true.
  - Case 2-2-2-2-2-3: The corresponding capability is available => the goal holds because R07 is applicable and so `cont(S)` reduces to true.

### Step 1-2: Consider which rule can be applied to the global state in the current case. 
 - Since there is a closed dependsOn capability, the next rule should be R05.

### Step 1-4: Split the current case into cases where the condition of the rule does or does not hold. 
 - The condition of R05 requires the parent node of the capability of idCP is created or started.

### Step 1-5: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the capability has a dangling `node` link, the current case should be split into following two cases:
   - Case 2-2-2-2-2-1-1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
   - Case 2-2-2-2-2-1-2: There is such a node.

### Step 1-4: Split the current case into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following three cases:
   - Case 2-2-2-2-2-1-2-1: the node of the capability is initial => the goal holds because of the Initial Cont Lemma.
   - Case 2-2-2-2-2-1-2-2: the node of the capability is created => the goal holds because R05 is applicable and so `cont(S)` reduces to true.
   - Case 2-2-2-2-2-1-2-3: the node of the capability is started => the goal holds because R05 is applicable and so `cont(S)` reduces to true.

### Case 2-3: The type of the unbound requirement is connectsTo.
### Step 1-2: Consider which rule can be applied to the global state in the current case. 
 - Since there is an unboud connectsTo requirement, the next rule should be R11.

### Step 1-3: Split the current case into cases which collectively cover the current case and one of which matches to LHS of the current rule.
 - LHS of R11 requires a relationship corresponding to the requirement.

### Step 1-5: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the requirement has a dangling `rel` link, the current case should be split into following two cases:
   - Case 2-3-1: There is no corresponding relationship => the goal holds because `wfs-allRQHaveRL(S)` reduces to false.
   - Case 2-3-2: There is a corresponding relationship.

### Step 1-3: Split the current case into cases which collectively cover the current case and one of which matches to LHS of the current rule.
 - Since LHS of R11 requires an open message, the current case should be split into following two cases:
  - Case 2-3-2-1: There is no corresponding open message.
  - Case 2-3-2-2: There is a corresponding open message => the goal holds because R11 is applicable and so `cont(S)` reduces to true.

### Step 1-5: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the open message has a dangling `cap` link, the current case should be split into following two cases:
   - Case 2-3-2-1-1: There is no corresponding capability => the goal holds because `wfs-allRLHaveCP(S)` reduces to false.
   - Case 2-3-2-1-2: There is a corresponding capability.
   
 - The current case should be split into following two cases:
   - Case 2-3-2-1-2-1: The node of the capability is the same as of the requirement => the goal holds because `wfs-allRLNotInSameND(S)` reduces to false.
   - Case 2-3-2-1-2-2: The node of the capability is different from the node of the requirement.

### Step 1-2: Consider which rule is applied to the global state in the current case. 
 - Since the next applicable rule depends on the local state of the connectsTo capability, the current case should be split into following three cases:
  - Case 2-3-2-1-2-2-1: The capability is closed.
  - Case 2-3-2-1-2-2-2: The capability is open.
  - Case 2-3-2-1-2-2-3: The capability is available => the goal holds because `inv-ifConnectsToCPAvailableThenRQWaitingReadyOrOpenMsg(S)` reduces to false.

### Case 2-3-2-1-2-2-1: The capability is closed.
### Step 1-2: Consider which rule is applied to the global state in the current case. 
 - Since there is a closed connectsTo capability, the next rule should be R09.

### Step 1-4: Split the current case into cases where the condition of the rule does or does not hold. 
 - The condition of R09 requires the parent node of the capability of idCP is created or started.

### Step 1-5: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the capability has a dangling `node` link, the current case should be split into following two cases:
   - Case 2-3-2-1-2-2-1-1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
   - Case 2-3-2-1-2-2-1-2: There is such a node.

### Step 1-4: Split the current case into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following three cases:
   - Case 2-3-2-1-2-2-1-2-1: the node of the capability is initial => the goal holds because of the Initial Cont Lemma.
   - Case 2-3-2-1-2-2-1-2-2: the node of the capability is created => the goal holds because R09 is applicable and so `cont(S)` reduces to true.
   - Case 2-3-2-1-2-2-1-2-3: the node of the capability is started => the goal holds because R09 is applicable and so `cont(S)` reduces to true.

### Case 2-3-2-1-2-2-2: The capability is open.
### Step 1-2: Consider which rule is applied to the global state in the current case. 
 - Since there is an open connectsTo capability, the next rule should be R10.

### Step 1-4: Split the current case into cases where the condition of the rule does or does not hold. 
-- The condition of R10 requires the parent node of the capability of idCP is started.

### Step 1-5: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the capability has a dangling `node` link, the current case should be split into following two cases:
   - Case 2-3-2-1-2-2-2-1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
   - Case 2-3-2-1-2-2-2-2: There is such a node.

### Step 1-4: Split the current case into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following three cases:
   - Case 2-3-2-1-2-2-2-2-1: the node of the capability is initial => the goal holds because of the Initial Cont Lemma.
   - Case 2-3-2-1-2-2-2-2-2: the node of the capability is created => the goal holds because `inv-ifConnectsToCPOpenThenRQWaitingOrOpenMsg(S)` reduces to false.
   - Case 2-3-2-1-2-2-2-2-3: the node of the capability is started => the goal holds because R10 is applicable and so `cont(S)` reduces to true.

### Case 3: One of requirements of the created node is waiting.
### Step 1-2: Consider which rule is applied to the global state in the current case. 
 - Since the next applicable rule depends on the type of the waiting requirement, the current case should be split into following three cases:
  - Case 3-1: The type of the waiting requirement is hostedOn => the goal holds because `inv-HostedOnRQNotWaiting(S)` reduces to false.
  - Case 3-2: The type of the waiting requirement is dependsOn.
  - Case 3-3: The type of the waiting requirement is connectsTo.

### Case 3-2: The type of the waiting requirement is dependsOn.
### Step 1-2: Consider which rule is applied to the global state in the current case. 
 - Since there is a waiting dependsOn requirement, the next rule should be R08.

### Step 1-3: Split the current case into cases which collectively cover the current case and one of which matches to LHS of the current rule.
 - LHS of R08 requires a relationship corresponding to the requirement and a capability corresponding to the relationship.

### Step 1-5: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the requirement has a dangling `rel` link, the current case should be split into following two cases:
   - Case 3-2-1: There is no corresponding relationship => the goal holds because `wfs-allRQHaveRL(S)` reduces to false.
   - Case 3-2-2: There is a corresponding relationship.

 - Since the relationship has a dangling `cap` link, the current case should be split into following two case   - Case 3-2-2-1: There is no corresponding capability => the goal holds because `wfs-allRLHaveCP(S)` reduces to false.
   - Case 3-2-2-2: There is a corresponding capability.
   
 - The current case should be split into following two cases:
   - Case 3-2-2-2-1: The node of the capability is the same as of the requirement => the goal holds because `wfs-allRLNotInSameND(S)` reduces to false.
   - Case 3-2-2-2-2: The node of the capability is different from the node of the requirement.

### Step 1-3: Split the current case into cases which collectively cover the current case and one of which matches to LHS of the current rule.
 - Since LHS of R08 requires an available capability corresponding to the requirement, the current case should be split into following three cases:
  - Case 3-2-2-2-2-1: The corresponding capability is closed => the goal holds because `inv-ifCPClosedThenRQUnbound(S)` reduces to false.
  - Case 3-2-2-2-2-2: The corresponding capability is open.
  - Case 3-2-2-2-2-3: The corresponding capability is available => the goal holds because R08 is applicable and so `cont(S)` reduces to true.

### Step 1-2: Consider which rule is applied to the global state in the current case. 
 - Since there is an open dependsOn capability, the next rule should be R06.

### Step 1-4: Split the current case into cases where the condition of the rule does or does not hold. 
 - The condition of R06 requires the parent node of the capability of idCP is started.

### Step 1-5: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the capability has a dangling `node` link, the current case should be split into following two cases:
   - Case 3-2-2-2-2-1-1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
   - Case 3-2-2-2-2-1-2: There is such a node.

### Step 1-4: Split the current case into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following three cases:
   - Case 3-2-2-2-2-1-2-1: the node of the capability is initial => the goal holds because of the Initial Cont Lemma.
   - Case 3-2-2-2-2-1-2-2: the node of the capability is created => the goal holds because DDSR02 of the created node includes another created node which is a contradiction.
   - Case 3-2-2-2-2-1-2-3: the node of the capability is started => the goal holds because R06 is applicable and so `cont(S)` reduces to true.

### Case 3-3: The type of the waiting requirement is connectsTo.
### Step 1-2: Consider which rule is applied to the global state in the current case. 
 - Since there is a waiting connectsTo requirement, the next rule should be R12.

### Step 1-3: Split the current case into cases which collectively cover the current case and one of which matches to LHS of the current rule.
 - LHS of R12 requires a relationship corresponding to the requirement.

### Step 1-5: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the requirement has a dangling `rel` link, the current case should be split into following two cases:
   - Case 3-3-1: There is no corresponding relationship => the goal holds because `wfs-allRQHaveRL(S)` reduces to false.
   - Case 3-3-2: There is a corresponding relationship.

### Step 1-3: Split the current case into cases which collectively cover the current case and one of which matches to LHS of the current rule.
 - Since LHS of R12 requires an available message corresponding to the requirement, the current case should be split into following two cases:
  - Case 3-3-2-1: There is no corresponding available message.
  - Case 3-3-2-2: There is a corresponding available message => the goal holds because R12 is applicable and so `cont(S)` reduces to true.

### Step 1-5: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the available message has a dangling `cap` link, the current case should be split into following two cases:
   - Case 3-3-2-1-1: There is no corresponding capability => the goal holds because `wfs-allRLHaveCP(S)` reduces to false.
   - Case 3-3-2-1-2: There is a corresponding capability.
   
 - The current case should be split into following two cases:
   - Case 3-3-2-1-2-1: The node of the capability is the same as of the requirement => the goal holds because `wfs-allRLNotInSameND(S)` reduces to false.
   - Case 3-3-2-1-2-2: The node of the capability is different from the node of the requirement.

### Step 1-2: Consider which rule is applied to the global state in the current case. 
 - Since the next applicable rule depends on the local state of the connectsTo capability, the current case should be split into following three cases:
  - Case 3-3-2-1-2-2-1: The capability is closed => the goal holds because `inv-ifCPClosedThenRQUnbound(S)` reduces to false.
  - Case 3-3-2-1-2-2-2: The capability is open.
  - Case 3-3-2-1-2-2-3: The capability is available => the goal holds because `inv-ifConnectsToCPAvailableThenRQReadyOrAvailableMsg(S)` reduces to false.
 
### Step 1-2: Consider which rule is applied to the global state in the current case. 
 - Since there is an open connectsTo capability, the next rule should be R10.

### Step 1-4: Split the current case into cases where the condition of the rule does or does not hold. 
 - The condition of R10 requires the parent node of the capability of idCP is started.

### Step 1-5: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the capability has a dangling `node` link, the current case should be split into following two cases:
   - Case 3-3-2-1-2-2-2-1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
   - Case 3-3-2-1-2-2-2-2: There is such a node.

### Step 1-4: Split the current case into cases where the condition of the rule does or does not hold. 
 - The current case should be split into following three cases:
   - Case 3-3-2-1-2-2-2-2-1: The node of the capability is initial => the goal holds because of the Initial Cont Lemma.
   - Case 3-3-2-1-2-2-2-2-2: The node of the capability is created => the goal holds because DDSR02 of the created node includes another created node which is a contradiction.
   - Case 3-3-2-1-2-2-2-2-3: The node of the capability is started => the goal holds because R10 is applicable and so `cont(S)` reduces to true.

## Proof of other lemmas (Proof-lemma.cafe)
- Omitted.
