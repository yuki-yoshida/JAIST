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
 - Since LHS of R02 requires a node corresponding to the requirement is created, the current case should be split into following cases:
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
 - Since LHS of R02 requires a node corresponding to the waiting requirement, the current case should be split into following cases:
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

## Condition (4)(5): init(S) implies inv(S) . inv(S) implies inv(SS) .の証明譜 (Proof-inv.cafe)
 - 各invariantはinv-AAA、各wfsはwfs-BBBという述語として定義しておく。
 - (4)(5)はinvariant毎に一つずつ証明するが、証明するinvariantをinvS(S)とする。
 - Condition (4)のゴールは、initinv = init implies invS .
 - Condition (5)のゴールは、iinv = inv and invS implies invS'.とし、invinvを二重否定イディオムを使って定義する。
 - 抽象レベルで証明済みのLemmaを利用するには、具象レベルにインスタンシエートする必要があるが、現在のところ、インスタンシエーションはCafeOBJの機能を利用するように整備されていないので、手作業が必要である。
 - 個々のinvariantの証明譜の説明は割愛する。

## Initial Cont Lemmaの証明譜(Proof-cyclelemma.cafe)
### ステップ 1-0: 証明すべき述語を定義
 - invcont = inv implies cont
 - Sにinitial nodeが含まれる時に、invcont(S)が成り立つことを証明する。

### ステップ 1-1: 最も一般的なケースから開始
 - 一つ以上のinitial nodeが存在する場合は、< (node(tnd, idND, initial) sND), sCP, sRQ, sRL, mp >が最も一般的な状態。
 - ここで、idND nodeは任意に選択しているので、Cyclic Dependency Lemmaが存在を保証する「initialであって、かつDDSR01にinitialなnodeが含まれないnode」であることを仮定してよい。

### Step 1-2 Consider which rule can be applied to the next state.
 - Since there is an initial node in the next state, the next rule should be R01.

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initial nodeのhostedOn requirementがすべてready」なので以下の3つにケース分けする。
  - Case 1: initial nodeのhostedOn requirementがすべてready => the goal holds because  (R01が適用可能なのでcont(S)がtrue)
  - Case 2: initial nodeのhostedOn requirementの一つがunbound.
  - Case 3: initial nodeのhostedOn requirementの一つがwaiting. =>  the goal holds because `inv-HostedOnRQNotWaiting(S)` reduces to false.

### Step 1-2: Consider which rule can be applied to the next state.
 - Since there is an unbound hostedOn requirement in the next state, the next rule should be R04.

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - requirementに対するrelationshipのリンクが未定なので、以下の２つにケース分けする
   - Case 2-1: There is no corresponding relationship => the goal holds because `wfs-allRQHaveRL(S)` reduces to false.
   - Case 2-2: There is a corresponding relationship.

 - relationshipに対するcapabilityのリンクが未定なので、以下の２つにケース分けする
   - Case 2-2-1: 対応するcapabilityが無い => the goal holds because `wfs-allRLHaveCP(S)` reduces to false.
   - Case 2-2-2: 対応するcapabilityがある
   
 - capabilityの親ノードのIDがすでに存在するものかどうかで、以下の２つにケース分けする
   - Case 2-2-2-1: capabilityの親ノードはrequirementの親ノードと同じ => the goal holds because `wfs-allRLNotInSameND(S)` reduces to false.
   - Case 2-2-2-2: capabilityの親ノードはrequirementの親ノードと異なる

### Step 1-3: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R04 requires a relationship corresponding to the available capability and an unbound requirement corresponding to the relationship, the current case should be split into following cases:
 - R04のLHSはrequiremntに対応するavailable capabilityが必要なので、cspコマンドで以下の３つにケース分けする。
  - Case 2-2-2-2-1: 対応するcapabilityがclosed
  - Case 2-2-2-2-2: 対応するcapabilityがopen => the goal holds because `inv-HostedOnCPNotOpen(S)` reduces to false.
  - Case 2-2-2-2-3: 対応するcapabilityがavailable => the goal holds because  (R04が適用可能なのでcont(S)がtrue)

### Step 1-2: Consider which rule can be applied to the next state.
 - Since there is a closed hostedOn capability in the next state, the next rule should be R03.

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親ノードのリンクが未定なので、以下の２つにケース分けする
   - Case 2-2-2-2-1-1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
   - Case 2-2-2-2-1-2: There is such a node.

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R03の条件節はcapabilityに対応するnodeがcreatedまたはstartedなので、以下の３つにケース分けする
   - Case 2-2-2-2-1-2-1: capabilityの親nodeがinitial => the goal holds because  (元のnodeのDDSR01にinitial nodeが存在して矛盾)
   - Case 2-2-2-2-1-2-2: capabilityの親nodeがcreated => the goal holds because  (R03が適用可能なのでcont(S)がtrue)
   - Case 2-2-2-2-1-2-3: capabilityの親nodeがstarted => the goal holds because  (R03が適用可能なのでcont(S)がtrue)

## Created Cont Lemmaの証明譜(Proof-cyclelemma.cafe)
### ステップ 1-0: 証明すべき述語を定義
 - invcont = inv implies cont
 - Sにcreated nodeが含まれる時に、invcont(S)が成り立つことを証明する。
 - 上記で証明済みのInitial Cont Lemmaを導入しておく。 

### ステップ 1-1: 最も一般的なケースから開始
 - 一つ以上のcreated nodeが存在する場合は、< (node(tnd, idND, created) sND), sCP, sRQ, sRL, mp >が最も一般的な状態。
 - ここで、idND nodeは任意に選択しているので、Cyclic Dependency Lemmaが存在を保証する「createdであって、かつDDSR02にcreatedなnodeが含まれないnode」であることを仮定してよい。

### Step 1-2: Consider which rule can be applied to the global state in the current case. 
 - Since there is a created node in the next state, the next rule should be R02.

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R02の条件節は「created nodeのrequirementがすべてready」なので以下の3つにケース分けする。
  - Case 1: created nodeのrequirementがすべてready => the goal holds because  (R02が適用可能なのでcont(S)がtrue)
  - Case 2: created nodeのrequirementの一つがunbound.
  - Case 3: created nodeのrequirementの一つがwaiting.

### Case 2: created nodeのrequirementの一つがunboundの証明。
### Step 1-2: Consider which rule can be applied to the global state in the current case. 
 - Since there is an available hostedOn capability in the next state, the next rule should be R04.
 - unboundなrequirementのタイプによって適用されるルールが異なるので、以下の３つにケース分け
  - Case 2-1: unboundなrequirementがhostedOn => the goal holds because `inv-ifNDCreatedThenHostedOnRQReady(S)` reduces to false.
  - Case 2-2: unboundなrequirementがdependsOn
  - Case 2-3: unboundなrequirementがconnectsTo

### Case 2-2: unboundなrequirementがdependsOnの証明
### Step 1-2: Consider which rule can be applied to the global state in the current case. 
 - Since there is an available hostedOn capability in the next state, the next rule should be R04.
 - unboundなdependsOn requirementがあるので、適用されるルールはR07。

### Step 1-3: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R04 requires a relationship corresponding to the available capability and an unbound requirement corresponding to the relationship, the current case should be split into following cases:
 - R07のLHSはrequiremntに対応するrelationishipと、されにそれに対応するcapabilityが必要。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - requirementに対するrelationshipのリンクが未定なので、以下の２つにケース分けする
   - Case 2-2-1: There is no corresponding relationship => the goal holds because `wfs-allRQHaveRL(S)` reduces to false.
   - Case 2-2-2: There is a corresponding relationship.

 - relationshipに対するcapabilityのリンクが未定なので、以下の２つにケース分けする
   - Case 2-2-2-1: 対応するcapabilityが無い => the goal holds because `wfs-allRLHaveCP(S)` reduces to false.
   - Case 2-2-2-2: 対応するcapabilityがある
   
 - capabilityの親ノードのIDがすでに存在するものかどうかで、以下の２つにケース分けする
   - Case 2-2-2-2-1: capabilityの親ノードはrequirementの親ノードと同じ => the goal holds because `wfs-allRLNotInSameND(S)` reduces to false.
   - Case 2-2-2-2-2: capabilityの親ノードはrequirementの親ノードと異なる

### Step 1-3: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R04 requires a relationship corresponding to the available capability and an unbound requirement corresponding to the relationship, the current case should be split into following cases:
 - R07のLHSはrequiremntに対応するactivatedなcapabilityが必要なので、cspコマンドで以下の３つにケース分けする。
  - Case 2-2-2-2-2-1: 対応するcapabilityがclosed
  - Case 2-2-2-2-2-2: 対応するcapabilityがopen => the goal holds because  (R07が適用可能なのでcont(S)がtrue)
  - Case 2-2-2-2-2-3: 対応するcapabilityがavailable => the goal holds because  (R07が適用可能なのでcont(S)がtrue)

### Step 1-2: Consider which rule can be applied to the global state in the current case. 
 - Since there is an available hostedOn capability in the next state, the next rule should be R04.
 - closedなdepensOn capabilityがあるので、適用されるルールはR05。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R05の条件節はcapabilityの親nodeがcreatedかstartedであることを要求する

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親ノードのリンクが未定なので、以下の２つにケース分けする
   - Case 2-2-2-2-2-1-1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
   - Case 2-2-2-2-2-1-2: There is such a node.

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R05の条件節はcapabilityに対応するnodeがcreatedまたはstartedなので、以下の３つにケース分けする
   - Case 2-2-2-2-2-1-2-1: capabilityの親nodeがinitial => the goal holds because  (Initial Cont Lemmaによりcont(S)がtrue)
   - Case 2-2-2-2-2-1-2-2: capabilityの親nodeがcreated => the goal holds because  (R05が適用可能なのでcont(S)がtrue)
   - Case 2-2-2-2-2-1-2-3: capabilityの親nodeがstarted => the goal holds because  (R05が適用可能なのでcont(S)がtrue)

### Case 2-3: unboundなrequirementがconnectsToの証明
### Step 1-2: Consider which rule can be applied to the global state in the current case. 
 - Since there is an available hostedOn capability in the next state, the next rule should be R04.
 - unboundなconnectsTo requirementがあるので、適用されるルールはR11。

### Step 1-3: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R04 requires a relationship corresponding to the available capability and an unbound requirement corresponding to the relationship, the current case should be split into following cases:
 - R11のLHSはrequiremntに対応するrelationishipが必要。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - requirementに対するrelationshipのリンクが未定なので、以下の２つにケース分けする
   - Case 2-3-1: There is no corresponding relationship => the goal holds because `wfs-allRQHaveRL(S)` reduces to false.
   - Case 2-3-2: There is a corresponding relationship.

### Step 1-3: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R04 requires a relationship corresponding to the available capability and an unbound requirement corresponding to the relationship, the current case should be split into following cases:
 - R11のLHSはrequiremntに対応するopen messageが必要なので、以下の2つにケース分けする。
  - Case 2-3-2-1: 対応するopen messageが無い
  - Case 2-3-2-2: 対応するopen messageがある => the goal holds because  (R11が適用可能なのでcont(S)がtrue)

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - open messageに対するcapabilityのリンクが未定なので、以下の２つにケース分けする
   - Case 2-3-2-1-1: 対応するcapabilityが無い => the goal holds because `wfs-allRLHaveCP(S)` reduces to false.
   - Case 2-3-2-1-2: 対応するcapabilityがある
   
 - capabilityの親ノードのIDがすでに存在するものかどうかで、以下の２つにケース分けする
   - Case 2-3-2-1-2-1: capabilityの親ノードはrequirementの親ノードと同じ => the goal holds because `wfs-allRLNotInSameND(S)` reduces to false.
   - Case 2-3-2-1-2-2: capabilityの親ノードはrequirementの親ノードと異なる

### ステップ 1-2: 次状態に適用されるルールを考察
 - connectsTo capabilityの状態によって適用されるルールが異なるので、以下の３つにケース分け
  - Case 2-3-2-1-2-2-1: Capabilityがclosed
  - Case 2-3-2-1-2-2-2: Capabilityがopen
  - Case 2-3-2-1-2-2-3: Capabilityがavailable => the goal holds because `inv-ifConnectsToCPAvailableThenRQWaitingReadyOrOpenMsg(S)` reduces to false.

### Case 2-3-2-1-2-2-1: Capabilityがclosedの証明
### ステップ 1-2: 次状態に適用されるルールを考察
 - closedなconnectsTo capabilityがあるので、適用されるルールはR09。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R09の条件節はcapabilityの親nodeがcreatedまたはstartedであることを要求する

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親ノードのリンクが未定なので、以下の２つにケース分けする
   - Case 2-3-2-1-2-2-1-1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
   - Case 2-3-2-1-2-2-1-2: There is such a node.

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R09の条件節はcapabilityに対応するnodeがcreatedまたはstartedなので、以下の３つにケース分けする
   - Case 2-3-2-1-2-2-1-2-1: capabilityの親nodeがinitial => the goal holds because  (Initial Cont Lemmaによりcont(S)がtrue)
   - Case 2-3-2-1-2-2-1-2-2: capabilityの親nodeがcreated => the goal holds because  (R09が適用可能なのでcont(S)がtrue)
   - Case 2-3-2-1-2-2-1-2-3: capabilityの親nodeがstarted => the goal holds because  (R09が適用可能なのでcont(S)がtrue)

### Case 2-3-2-1-2-2-2: Capabilityがopenの証明
### ステップ 1-2: 次状態に適用されるルールを考察
 - openなconnectsTo capabilityがあるので、適用されるルールはR10。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R10の条件節はcapabilityの親nodeがstartedであることを要求する

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親ノードのリンクが未定なので、以下の２つにケース分けする
   - Case 2-3-2-1-2-2-2-1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
   - Case 2-3-2-1-2-2-2-2: There is such a node.

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R09の条件節はcapabilityに対応するnodeがcreatedまたはstartedなので、以下の３つにケース分けする
   - Case 2-3-2-1-2-2-2-2-1: capabilityの親nodeがinitial => the goal holds because  (Initial Cont Lemmaによりcont(S)がtrue)
   - Case 2-3-2-1-2-2-2-2-2: capabilityの親nodeがcreated => the goal holds because `inv-ifConnectsToCPOpenThenRQWaitingOrOpenMsg(S)` reduces to false.
   - Case 2-3-2-1-2-2-2-2-3: capabilityの親nodeがstarted => the goal holds because  (R10が適用可能なのでcont(S)がtrue)

### Case 3: created nodeのrequirementの一つがwaitingの証明。
### ステップ 1-2: 次状態に適用されるルールを考察
 - waitingなrequirementのタイプによって適用されるルールが異なるので、以下の３つにケース分け
  - Case 3-1: waitingなrequirementがhostedOn => the goal holds because `inv-HostedOnRQNotWaiting(S)` reduces to false.
  - Case 3-2: waitingなrequirementがdependsOn
  - Case 3-3: waitingなrequirementがconnectsTo

### Case 3-2: waitingなrequirementがdependsOnの証明
### ステップ 1-2: 次状態に適用されるルールを考察
 - waitingなdependsOn requirementがあるので、適用されるルールはR08。

### Step 1-3: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R04 requires a relationship corresponding to the available capability and an unbound requirement corresponding to the relationship, the current case should be split into following cases:
 - R08のLHSはrequiremntに対応するrelationishipと、されにそれに対応するcapabilityが必要。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - requirementに対するrelationshipのリンクが未定なので、以下の２つにケース分けする
   - Case 3-2-1: There is no corresponding relationship => the goal holds because `wfs-allRQHaveRL(S)` reduces to false.
   - Case 3-2-2: There is a corresponding relationship.

 - relationshipに対するcapabilityのリンクが未定なので、以下の２つにケース分けする
   - Case 3-2-2-1: 対応するcapabilityが無い => the goal holds because `wfs-allRLHaveCP(S)` reduces to false.
   - Case 3-2-2-2: 対応するcapabilityがある
   
 - capabilityの親ノードのIDがすでに存在するものかどうかで、以下の２つにケース分けする
   - Case 3-2-2-2-1: capabilityの親ノードはrequirementの親ノードと同じ => the goal holds because `wfs-allRLNotInSameND(S)` reduces to false.
   - Case 3-2-2-2-2: capabilityの親ノードはrequirementの親ノードと異なる

### Step 1-3: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R04 requires a relationship corresponding to the available capability and an unbound requirement corresponding to the relationship, the current case should be split into following cases:
 - R08のLHSはrequiremntに対応するavailableなcapabilityが必要なので、cspコマンドで以下の３つにケース分けする。
  - Case 3-2-2-2-2-1: 対応するcapabilityがclosed => the goal holds because `inv-ifCPClosedThenRQUnbound(S)` reduces to false.
  - Case 3-2-2-2-2-2: 対応するcapabilityがopen
  - Case 3-2-2-2-2-3: 対応するcapabilityがavailable => the goal holds because  (R08が適用可能なのでcont(S)がtrue)

### ステップ 1-2: 次状態に適用されるルールを考察
 - openなdepensOn capabilityがあるので、適用されるルールはR06。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R06の条件節はcapabilityの親nodeがstartedであることを要求する

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親ノードのリンクが未定なので、以下の２つにケース分けする
   - Case 3-2-2-2-2-1-1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
   - Case 3-2-2-2-2-1-2: There is such a node.

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R05の条件節はcapabilityに対応するnodeがcreatedまたはstartedなので、以下の３つにケース分けする
   - Case 3-2-2-2-2-1-2-1: capabilityの親nodeがinitial => the goal holds because  (Initial Cont Lemmaによりcont(S)がtrue)
   - Case 3-2-2-2-2-1-2-2: capabilityの親nodeがcreated => the goal holds because  (元のnodeのDDSR02にcreated nodeが存在して矛盾)
   - Case 3-2-2-2-2-1-2-3: capabilityの親nodeがstarted => the goal holds because  (R06が適用可能なのでcont(S)がtrue)

### Case 3-3: waitingなrequirementがconnectsToの証明
### ステップ 1-2: 次状態に適用されるルールを考察
 - waitingなconnectsTo requirementがあるので、適用されるルールはR12。

### Step 1-3: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R04 requires a relationship corresponding to the available capability and an unbound requirement corresponding to the relationship, the current case should be split into following cases:
 - R12のLHSはrequiremntに対応するrelationishipが必要。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - requirementに対するrelationshipのリンクが未定なので、以下の２つにケース分けする
   - Case 3-3-1: There is no corresponding relationship => the goal holds because `wfs-allRQHaveRL(S)` reduces to false.
   - Case 3-3-2: There is a corresponding relationship.

### Step 1-3: Split the current case into cases which collectively cover the current case and the next state of one of the split cases matches to LHS of the current rule.
 - Since LHS of R04 requires a relationship corresponding to the available capability and an unbound requirement corresponding to the relationship, the current case should be split into following cases:
 - R11のLHSはrequiremntに対応するavailable messageが必要なので、以下の2つにケース分けする。
  - Case 3-3-2-1: 対応するavailable messageが無い
  - Case 3-3-2-2: 対応するavailable messageがある => the goal holds because  (R12が適用可能なのでcont(S)がtrue)

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - available messageに対するcapabilityのリンクが未定なので、以下の２つにケース分けする
   - Case 3-3-2-1-1: 対応するcapabilityが無い => the goal holds because `wfs-allRLHaveCP(S)` reduces to false.
   - Case 3-3-2-1-2: 対応するcapabilityがある
   
 - capabilityの親ノードのIDがすでに存在するものかどうかで、以下の２つにケース分けする
   - Case 3-3-2-1-2-1: capabilityの親ノードはrequirementの親ノードと同じ => the goal holds because `wfs-allRLNotInSameND(S)` reduces to false.
   - Case 3-3-2-1-2-2: capabilityの親ノードはrequirementの親ノードと異なる

### ステップ 1-2: 次状態に適用されるルールを考察
 - connectsTo capabilityの状態によって適用されるルールが異なるので、以下の３つにケース分け
  - Case 3-3-2-1-2-2-1: Capabilityがclosed => the goal holds because `inv-ifCPClosedThenRQUnbound(S)` reduces to false.
  - Case 3-3-2-1-2-2-2: Capabilityがopen
  - Case 3-3-2-1-2-2-3: Capabilityがavailable => the goal holds because `inv-ifConnectsToCPAvailableThenRQReadyOrAvailableMsg(S)` reduces to false.
 
### ステップ 1-2: 次状態に適用されるルールを考察
 - openなconnectsTo capabilityがあるので、適用されるルールはR10。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R10の条件節はcapabilityの親nodeがstartedであることを要求する

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親ノードのリンクが未定なので、以下の２つにケース分けする
   - Case 3-3-2-1-2-2-2-1: There is no such node => the goal holds because `wfs-allCPHaveND(S)` reduces to false.
   - Case 3-3-2-1-2-2-2-2: There is such a node.

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R09の条件節はcapabilityに対応するnodeがcreatedまたはstartedなので、以下の３つにケース分けする
   - Case 3-3-2-1-2-2-2-2-1: capabilityの親nodeがinitial => the goal holds because  (Initial Cont Lemmaによりcont(S)がtrue)
   - Case 3-3-2-1-2-2-2-2-2: capabilityの親nodeがcreated => the goal holds because  (元のnodeのDDSR02にcreated nodeが存在して矛盾)
   - Case 3-3-2-1-2-2-2-2-3: capabilityの親nodeがstarted => the goal holds because  (R10が適用可能なのでcont(S)がtrue)

## その他のLemmaの証明譜(Proof-lemma.cafe)

以上で、すべての十分条件が証明済みとなり、init leads-to finalが証明できた。

