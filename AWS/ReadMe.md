# Verification Sample for a leads-to property of AWS CloudFormation
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
     = wfs-atLeastOneRS(S) and
       wfs-uniqRS(S) and wfs-uniqPR(S) and 
       wfs-allPRHaveRS(S) and wfs-allPRHaveRRS(S) .
  eq init(< SetRS,SetPR >)
     = wfs(< SetRS,SetPR >) and
       noRSCycle(< SetRS,SetPR >) and
       allRSInStates(SetRS,initial) and 
       allPRInStates(SetPR,notready) .
  eq final(< SetRS,SetPR >)
     = allRSInStates(SetRS,started) .
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
  eq m(< SetRS,SetPR >)
     = #ResourceInStates(initial,SetRS) + #PropertyInStates(notready,SetPR) .
  ```

### Step 0-4: Define `inv(S)`.
 - Each of wfs's and invariants is recommended to define as inv-AAA(S) or wfs-BBB(S).
 - Define `inv(S)` as follows using CITP Technique (1) ii.

  ```
  ceq inv(S) = false if not wfs-atLeastOneRS(S) .
  ceq inv(S) = false if not wfs-allPRHaveRS(S) .
  ceq inv(S) = false if not wfs-allPRHaveRRS(S) .
  ceq inv(S) = false if not inv-ifRSStartedThenPRReady(S) .
  ```

### Step 0-5: Prepare for using the Cyclic Dependency Lemma.
 - Prepare a nonexec lemma which means that `DDS` of a specified initial resource never includes other initial resources.

  ```
  ceq [Cycle :nonexec]: 
     true = false if someRSInStates(DDSC(res(T, IDRS, initial),S),initial) .
  ```

### Step 0-6: Prepare arbitrary constants.

  ```
  ops idRS idRS' idRS1 : -> RSIDLt
  ops idRRS idRRS' idRRS1 : -> RSIDLt
  ops idPR idPR' idPR1 : -> PRIDLt
  ops sRS sRS' sRS'' sRS''' : -> SetOfResource
  ops sPR sPR' sPR'' sPR''' : -> SetOfProperty
  ops trs trs' trs'' trs''' : -> RSType
  ops tpr tpr' tpr'' tpr''' : -> PRType
  ops srs srs' srs'' srs''' : -> RSState
  ops spr spr' spr'' spr''' : -> PRState
  op stRS : -> SetOfRSState
  op stPR : -> SetOfPRState
  op x : -> Resource
  ```

## Proof of Condition (1): `init(S) implies cont(S)` (Proof-initcont.cafe)
### Step 1-0: Define a predicate to be proved.

  ```
  eq initcont(S) = init(S) implies cont(S) .
  ```

### Step 1-1: Begin with the most general case. 
 - Let `sRS` be a proof constant of sort `SetOfResource` and `sPR` a proof constant of sort `SetOfProperty`.
 - The most general state can be represented as `< sRS, sPR >`.

  ```
  :goal {eq initcont(< sRS, sPR >) = true .}
  ```

### Step 1-2: Consider which rule is applied to the global state in the current case. 
 - The first rule is R01.

### Step 1-3: Split the current case into cases which collectively cover the current case and one of which matches to LHS of the current rule.
 - Since LHS of R01 requires at least one initial resources, the root case should be split into following three cases:
  - Case 1: When there is no resource => the goal holds because `init(S)` reduces to false.
  - Case 2-1: When at least one initial resource.
  - Case 2-2: When at least one started resource => the goal holds because `init(S)` reduces to false.

### Step 1-4: Split the current case into cases where the condition of the rule does or does not hold. 
 - Since the conditional clause of R01 requires that all properties of the initial resource are ready, the current case should be split into following two cases:
  - Case 2-1-1: All properties of the initial resource are ready => the goal holds because R01 is applicable and so `cont(S)` reduces to true.
  - Case 2-1-2: At least one property of the initial resource is not-ready.

### Step 1-5: When there is a dangling link, split the current case into cases where the linked object does or does not exist.
 - Since the not-ready property has a dangling `refer` link, the current case should be split into following three cases:
  - Case 2-1-2-1: When the resource referred by the property does not exist => the goal holds because `wfs-allPRHaveRRS(S)` reduces to false and so `inv(S)` reduces to false.
  - Case 2-1-2-2-1: When the resource idRRS referred by the property is initial.
  - Case 2-1-2-2-1: When the resource idRRS referred by the property is started => the goal holds because `init(S)` reduces to false.

### Step 1-6: When falling in a cyclic situation, use the Cyclic Dependency Lemma.
 - Since resource idRS is an arbitrary initial resource introduced in Case 2-1, the CDL assures that DDS of the resource does not include any other initial resources.
 - Introduce the prepared nonexec lemma specifying resource idRS.

  ```
  :init [Cycle] by {
    T:RSType <- trs;
    IDRS:RSID <- idRS;
    S:State <- < sRS, sPR >;
  }
  ```

 - The goal holds because DDS of idRS includes an initial resource, idRRS, referred by the `refer` link.

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

## Proof of Condition (2) for R01 (Proof-contcont-R01.cafe)
### Step 2-1: Begin with the cases each of which matches to LHS of each rule.
 - The most general state matching to LHS of R01 can be represented by replacing all variables of the LHS by proof constants.

  ```
  :goal { eq contcont(< (res(trs,idRS,initial) sRS), sPR >) = true . }
  ```

### Step 2-2: Split the current case for a rule into cases where the condition of the rule does or does not hold. 
 - The root case should be split into following two cases:
  - Case 1: All properties of the initial resource are ready.
  - Case 2: Not all properties of the initial resource are ready => the goal holds because there is no next state.

### Step 2-3: Split the current case into cases where predicate `final` does or does not hold in the next state.
 - Since the next state includes one started resource and so `final(SS)` holds when all of the rest resources are started, the current case should be split into following two cases:
  - Case 1-1: When all of the other resources are started => the goal holds because `final(SS)` reduces to true.
  - Case 1-2: When there is an initial resource.

### Step 2-4: Think which rule can be applied to the next state.
 - The next rule should be R01 for the initial resource of idRS'.

### Step 2-5: Split the general case into cases which collectively cover the general case and one of which matches to LHS of the applicable rule.
 - The case already matches to LHS of R01.

### Step 2-6: Split the general case into cases where the condition of the applicable rule does or does not hold.
 - Since the conditional clause of R01 requires that all properties of the initial resource are ready, the current case should be split into following two cases:
  - Case 1-2-1: All properties of the initial resource are ready => the goal holds because R01 is applicable to the next state and so `cont(SS)` reduces to true.
  - Case 1-2-2: At least one property of the initial resource is not-ready.

### Because sPR is redefined, allPROfRSInStates(sPR,idRS,ready) should be claimed again using CITP Technique (2) as follows:

  ```
  :set(normalize-init,on)
  :init ( ceq B1:Bool = true if not B2:Bool . ) by {
    B1:Bool <- allPROfRSInStates(sPR,idRS,ready) ;
    B2:Bool <- allPROfRSInStates(sPR,idRS,ready) == true ;
  }
  :set(normalize-init,off)
  ```

### Step 2-7: When there is a dangling link, split the case into cases where the linked object does or does not exist.
 - Since the not-ready property has a dangling `refer` link, the current case should be split into following three cases:
  - Case 1-2-2-1: When the resource referred by the property does not exist => the goal holds because `wfs-allPRHaveRRS(S)` reduces to false and so `inv(S)` reduces to false.
  - Case 1-2-2-2-1: When the resource idRRS referred by the property is initial.
  - Case 1-2-2-2-2: When the resource idRRS referred by the property is started => the goal holds because R02 is applicable to the next state and so `cont(SS)` reduces to true.

### Step 2-8: When falling in a cyclic situation, use the Cyclic Dependency Lemma.
 - Since resource idRS is an arbitrary initial resource introduced in Case 1-2, the CDL assures that DDS of the resource does not include any other initial resources.
 - Introduce the prepared nonexec lemma specifying resource idRS'.

  ```
  :init [Cycle] by {
    T:RSType <- trs';
    IDRS:RSID <- idRS';
    S:State <- < (res(trs,idRS,initial) sRS), sPR >;
  }
  ```

 - The goal holds because DDS of idRS' includes an initial resource, idRRS, referred by the `refer` link.

## Proof of Condition (2) for R02 (Proof-contcont-R02.cafe)
### Step 2-1: Begin with the cases each of which matches to LHS of each rule.

  ```
  :goal {
    eq contcont(< (res(trs,idRRS,started) sRS), 
                  (prop(tpr,idPR,notready,idRS,idRRS) sPR) >) = true .
  }
  ```

### Step 2-2: Split the most general case for a rule into cases where the condition of the rule does or does not hold.
 - Since R02 is unconditional, this step is ignored.

### Step 2-3: Split the rule applied case into cases where predicate final does or does not hold in the next state.
 - Since the next state after applying R02 includes a started resource, it would be final if all the rest resources are started. But it is not the case because we know a not-ready property has an initial parent resource.

### Step 2-7: When there is a dangling link, split the case into cases where the linked object does or does not exist.
 - Since the property becoming ready has a dangling `parent` link, the current case should be split into following three cases:
 - Case 1: When the resource referred by the property does not exist => the goal holds because `wfs-allPRHveRS(S)` reduce to false and s `inv(S)` reduces to false.
 - Case 2-1: When the resource idRS referred by the property is initial.
 - Case 2-2: When the resource idRS referred by the property is started => the goal holds because R02 is applicable to the next state.

### Preparing to use the Cyclic Dependency Lemma.
 - Since Case 2-1 includes initial resource idRS, the Cyclic Depenency Lemma ensures there is an initial resource R where DDSC(R,S) does not include any initial nodes.
 - Assuming R = `res(trs'',idRS1,initial)`, decompose `sRS'` into R and `sRS''` as follows:

  ```
  :init ( eq SRS:SetOfResource = (RS:Resource SRS':SetOfResource) . ) by {
    SRS:SetOfResource <- sRS';
    SRS':SetOfResource <- sRS'';
    RS:Resource <- res(trs'',idRS1,initial);
  }
  ```

### Step 2-4: Think which rule can be applied to the next state.
 - The next rule should be R01 for the initial resource of idRS1.

### Step 2-5: Split the general case into cases which collectively cover the general case and one of which matches to LHS of the applicable rule.
 - The case already matches to LHS of R01.

### Step 2-6: Split the general case into cases where the condition of the applicable rule does or does not hold.
 - Since the conditional clause of R01 requires that all properties of the initial resource are ready, the current case should be split into following two cases:
 - 
 - Case 2-1-1: When all the properties of the resource idRS1 are ready => the goal holds because R01 is applicable to the next state and so `cont(SS)` reduces to true.
 - Case 2-1-2: When one of the properties of the resource idRS1 are not-ready.

### Step 2-7: When there is a dangling link, split the case into cases where the linked object does or does not exist.
 - Since the not-ready property idPR1 has a dangling `refer` link idRRS1, the current case should be split into following three cases:
  - Case 2-1-2-1: When the resource referred by the property does not exist => the goal holds because `wfs-allPRHaveRRS(S)` reduces to false and so `inv(S)` reduces to false.
  - Case 2-1-2-2-1: When the resource idRRS1 referred by the property is initial.
  - Case 2-1-2-2-2: When the resource idRRS1 referred by the property is started => the goal holds because R02 is applicable to the next state and so `cont(SS)` reduces to true.

### Step 2-8: When falling in a cyclic situation, use the Cyclic Dependency Lemma.
 - Introduce the prepared nonexec lemma specifying resource idRS'.

  ```
  :init [Cycle] by {
    T:RSType <- trs'';
    IDRS:RSID <- idRS1;
    S:State <- < (res(trs, idRRS, started) sRS),
                 (prop(tpr,idPR,notready,idRS,idRRS) sPR) >;
  }
  ```

 - The goal holds because DDS of idRS1 includes an initial resource, idRRS1, referred by the `refer` link.

## Proof of Condition (3): `inv(S) and not final(S) implies m(S) > m(SS)` (Proof-measure.cafe)
### Step 3-0: Use natural number axioms.
 - Protecting include module NATAXIOM provided by the framework.

### Step 3-1: Define a predicate to be proved.

  ```
  eq mmes(S,SS)
     = inv(S) and not final(S) implies m(S) > m(SS) .

  pred mesmes : State .
  eq mesmes(S)
     = not (S =(*,1)=>+ SS if CC suchThat
            not ((CC implies mmes(S,SS)) == true)
     	   { S => SS !! CC ! inv(S) ! final(S) ! (m(S) > m(SS)) }) .
  ```

## Proof of Condition (3) for R01
### Step 3-2: Begin with the cases each of which matches to LHS of each rule.

  ```
  :goal { eq mesmes(< (res(trs,idRS,initial) sRS), sPR >) = true . }
  ```

### Step 3-3: Split the most general case for a rule into cases where the condition of the rule does or does not hold. 
 - Since the conditional clause of R01 requires that all properties of the initial resource are ready, the current case should be split into following two cases:
 - 
 - Case 1: When all the properties of the resource idRS are ready => the goal holds because R01 is applicable to the current state and `m(S) > m(SS)` reduces to true.
 - Case 2: When one of the properties of the resource idRS1 are not-ready => the goal holds because there is no next state.

## Proof of Condition (3) for R02
### Step 3-2: Begin with the cases each of which matches to LHS of each rule.

  ```
  :goal {
    eq mesmes(< (res(trs,idRRS,started) sRS), 
                (prop(tpr,idPR,notready,idRS,idRRS) sPR) >) = true .
  }
  ```

 - The goal holds because `m(S) > m(SS)` reduces to true.

## Proof of Condition (4): `inv(S) and (cont(S) or final(S)) and m(S) = 0 implies final(S)` (Proof-measure.cafe)
### Step 4-0: Use a natural number axiom.
 - Protecting include module NATAXIOM provided by the framework.

### Step 4-1: Define a predicate to be proved.

  ```
  eq mesfinal(S)
     = inv(S) and cont(S) and m(S) = 0 implies final(S) .
  ```

## Proof of Condition (4) for R01
### Step 4-2: Begin with the cases each of which matches to LHS of each rule.

  ```
  :goal {  eq mesfinal(< (res(trs,idRS,initial) sRS), sPR >) = true . }
  ```

 - The goal holds because `m(S) = 0` reduces to false.

## Proof of Condition (4) for R02
### Step 4-2: Begin with the cases each of which matches to LHS of each rule.

  ```
  :goal {  eq mesfinal(< (res(trs,idRS,initial) sRS), sPR >) = true . }
  ```
 - The goal holds because `m(S) = 0` reduces to false.

## Proof of Condition (5)(6): `init(S) implies inv(S) . inv(S) implies inv(SS) .` (Proof-inv.cafe)
### Step 5-0,6-0: Define a predicate to be proved.

  ```
  eq initinv(S)
     = init(S) implies invK(S) .
  eq iinv(S,SS)
     = inv(S) and invK(S) implies invK(SS) .
  eq invinv(S)
     = not (S =(*,1)=>+ SS if CC suchThat
            not ((CC implies iinv(S,SS)) == true)
     	   { S => SS !! CC ! inv(S) ! invK(S) ! invK(SS) }) .
  ```

 - Condition (5)(6) are proved for each invariants and `invK` above will be defined as the target invariant.

## Proof of Condition (5)(6) for inv-ifRSStartedThenPRReady.
 - Define `invK` to be `inv-ifRSStartedThenPRReady`.

  ```
  eq invK(S) = inv-ifRSStartedThenPRReady(S) .
  ```

 - Instantiate general lemma `m2o-lemma07` which means that all the properties of a started resource are ready when all resources are initial and not started.

  ```
  eq [m2o-lemma07]:
      (allRSInStates(SetRS,initial) and 
       ifRSInStatesThenPRInStates(SetRS,started,SetPR,ready))
    = allRSInStates(SetRS,initial) .
  ```

 - Instantiate general lemma `m2o-lemma11` which means that all the properties of a started resource keep to be ready when a not-ready property transits to be ready.

  ```
  eq [m2o-lemma11]:
     (ifRSInStatesThenPRInStates(SetRS, started, (prop(TPR,IDPR,notready,IDRS,IDRRS) SetPR), ready) and
      ifRSInStatesThenPRInStates(SetRS, started, (prop(TPR,IDPR,   ready,IDRS,IDRRS) SetPR), ready))
    = ifRSInStatesThenPRInStates(SetRS, started, (prop(TPR,IDPR,notready,IDRS,IDRRS) SetPR), ready) .
  ```

## Proof of Condition (5) for inv-ifRSStartedThenPRReady.
### Step 5-2: Begin with the most general case. 

  ```
  :goal { eq initinv(< sRS,sPR >) = true . }
  ```

 - The goal holds because of `m2o-lemma07`.

## Proof of Condition (6) for inv-ifRSStartedThenPRReady and R01
###  Step 6-2: Begin with the cases each of which matches to LHS of each rule.

  ```
  :goal { eq invinv(< (res(trs,idRS,initial) sRS), sPR >) = true . }
  ```

### Step 6-3: Split the most general case for a rule into cases  where the condition of the rule does or does not hold. 
 - Since the conditional clause of R01 requires that all properties of the initial resource are ready, the current case should be split into following two cases:
  - Case 1-1: The is no properties of the initial resource => the goal holds because the initial resource transits to be started but it has no properties.
  - Case 1-2: All properties of the initial resource are ready => the goal holds because the initial resource transits to be started but all of its properties are ready.
  - Case 2: At least one property of the initial resource is not-ready => the goal holds because no next state.

## Proof of Condition (6) for inv-ifRSStartedThenPRReady and R02
###  Step 6-2: Begin with the cases each of which matches to LHS of each rule.

  ```
  :goal {
    eq invinv(< (res(trs,idRRS,started) sRS), 
                (prop(tpr,idPR,notready,idRS,idRRS) sPR) >) = true .
  }
  ```

 - Case 1: The goal holds because `invS(S) implies invS(SS)` holds by `m2o-lemma11`.

## Proof of Condition (5)(6) for wfs-allPRHaveRSのCondition.
## Proof of Condition (5)(6) for wfs-allPRHaveRRSのCondition.
## Proof of Condition (5)(6) for wfs-atLeastOneRSのCondition.
 - Almost the same as above.

Thus all the sufficient conditions have been proved, which means that `init leads-to final` holds.
