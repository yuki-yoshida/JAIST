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

### Step 1-2: Think which rule is applied to the initial state in an unproved case. 
 - The first rule is R01.

### Step 1-3: Split the general case into cases which collectively cover the general case and one of which matches to LHS of the first rule.
 - Since LHS of R01 requires at least one initial resources, the root case should be split into following three cases:
  - Case 1: When there is no resource => the goal holds because `init(S)` reduces to false.
  - Case 2-1: When at least one initial resource.
  - Case 2-2: When at least one started resource => the goal holds because `init(S)` reduces to false.

### Step 1-4: Split the first rule case into cases where the condition of the rule does or does not hold.
 - Since the conditional clause of R01 requires that all properties of the initial resource are ready, the current case should be split into following two cases:
  - Case 2-1-1: All properties of the initial resource are ready => the goal holds because R01 is applicable and so `cont(S)` reduces to true.
  - Case 2-1-2: At least one property of the initial resource is notready.

### Step 1-5: When there is a dangling link, split the case into cases where the linked object does or does not exist.
 - Since the notready property has a dangling `refer` link, the current case should be split into following three cases:
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
  :goal {
    eq contcont(< (res(trs,idRS,initial) sRS), sPR >) = true .
  }
  ```

### Step 2-2: Split the most general case for a rule into cases where the condition of the rule does or does not hold.
 - The root case should be split into following two cases:
  - Case 1: All properties of the initial resource are ready.
  - Case 2: Not all properties of the initial resource are ready => the goal holds because there is no next state.

### Step 2-3: Split the rule applied case into cases where predicate final does or does not hold in the next state.
 - Since the next state includes one started resource and so `final(S')` holds when all of the rest resources are started, the current case should be split into following two cases:
  - Case 1-1: When all of the other resources are started => the goal holds because `final(S')` reduces to true.
  - Case 1-2: When there is an initial resource.

### Step 2-4: Think which rule can be applied to the next state.
 - The next rule should be R01 for the initial resource of idRS'.

### Step 2-5: Split the general case into cases which collectively cover the general case and one of which matches to LHS of the applicable rule.
 - The case already matches to LHS of R01.

### Step 2-6: Split the general case into cases where the condition of the applicable rule does or does not hold.
 - Since the conditional clause of R01 requires that all properties of the initial resource are ready, the current case should be split into following two cases:
  - Case 1-2-1: All properties of the initial resource are ready => the goal holds because R01 is applicable to the next state and so `cont(S')` reduces to true.
  - Case 1-2-2: At least one property of the initial resource is notready.

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
 - Since the notready property has a dangling `refer` link, the current case should be split into following three cases:
  - Case 1-2-2-1: When the resource referred by the property does not exist => the goal holds because `wfs-allPRHaveRRS(S)` reduces to false and so `inv(S)` reduces to false.
  - Case 1-2-2-2-1: When the resource idRRS referred by the property is initial.
  - Case 1-2-2-2-2: When the resource idRRS referred by the property is started => the goal holds because R02 is applicable to the next state and so `cont(S')` reduces to true.

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

## R02に対するCondition (2)の証明譜 (Proof-contcont-R02.cafe)
### ステップ 2-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R02のLHSを任意定数trs, idRRS, sRS, tpr, idPR, idRS, sPRで表現する。

### ステップ 2-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R02は無条件ルールなので、ケース分けは不要。

### ステップ 2-3: ルール適用後の次状態がfinalになる/ならないでケース分け
 - R02適用後にはstartedリソースが一つあるので、残りのリソースが全部startedならfinalになる。そこで、以下の２つにケース分けする。
 - Case 1: 残りのリソースすべてがstarted => 証明可能 (final(S')がtrue)
 - Case 2: 残りのリソースすべてがstarted、ではない

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - readyになったプロパティのparentリンクが未定なので、以下の３つにケース分けする
 - Case 2-1: parentリンクの参照先が存在しない => 証明可能 (wfs-allPRHaveRRS(S)がfalse)
 - Case 2-2-1: parentリンクの参照先リソースが存在してinitial
 - Case 2-2-2: referリンクの参照先リソースが存在してstarted

### CDL適用の準備
 - ここでCase 2-2-1にはinitialリソースが存在するのでCDLを適用できるが、このinitialリソースは任意に選択したものではないので、CDL適用対象のinitialリソースを別に用意する必要がある。
 - sRS'を分解してCDL適用対象リソースidRS1を導入する。

### ステップ 2-4: 次状態に適用されるルールを考察
 - initialリソースがあるので、適用されるルールはR01。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initialリソースのプロパティがすべてready」なので以下の２つにケース分けする。
 - Case 2-2-1-1: initialリソースのプロパティがすべてready => 証明可能 (次状態にR01が適用可能)
 - Case 2-2-1-2: initialリソースのプロパティのうちnotreadyなものが少なくとも一つある

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - notreadyプロパティのreferリンクが未定なので、以下の３つにケース分けする
 - Case 2-2-1-2-1: referリンクの参照先が存在しない => 証明可能 (wfs-allPRHaveRRS(S)がfalse)
 - Case 2-2-1-2-2-1: referリンクの参照先リソースが存在してinitial
 - Case 2-2-1-2-2-2: referリンクの参照先リソースが存在してstarted => 証明可能 (次状態にR02が適用可能)

### ステップ 2-5: 循環する状況になったらCyclic Dependency Lemmaを適用
 - Case 2-2-1で導入したリソースのDDSに、referリンクの参照先リソースが含まれるので、矛盾が生じ、証明が完了する。

## Condition (3): inv(S) and not final(S) implies m(S) > m(SS) の証明譜 (Proof-measure.cafe)
### ステップ 3-0: 証明すべき述語を定義
 - mmes = inv and not final implies m > m'
 - 次状態が存在する状態に関する条件なので、前件にcont(S)が不要であることに注意。
 - mesmesを二重否定イディオムを使って定義する。
 - 自然数に対するAxiomとして N < N+1 を定義しておく。

## R01に対するCondition (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R01のLHSを任意定数trs, idRS, sRS, sPRで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initialリソースのプロパティがすべてready」なので以下の２つにケース分けする。
 - Case 1: initialリソースのプロパティがすべてready => 証明可能 (m(S) > m(SS)が成り立つ)
 - Case 2: initialリソースのプロパティがすべてready、ではない => 証明可能 (次状態が無い)

## R02に対するCondition (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R02のLHSを任意定数trs, idRRS, sRS, tpr, idPR, idRS, sPRで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R02は無条件ルールなので、ケース分けは不要。
 - Case 1: R02のLHSにマッチする最も一般的なケース => 証明可能 (m(S) > m(SS)が成り立つ)

## Condition (4): inv(S) and (cont(S) or final(S)) and m(S) = 0 implies final(S) の証明譜 (Proof-measure.cafe)
### ステップ 4-0: 証明すべき述語を定義
 - mesfinal = inv and (cont or final) and m = 0 implies final .

### ステップ 4-1: m(S)用の一般Lemmaをインスタンシエート
 - initialリソースの数が0ならば、すべてのリソースはstartedである。

### ステップ 4-2: 自然数に対するAxiomを定義
 - 「N1 + N2 = 0」と「N1 = 0 かつ N2 = 2」が等価である。

## Condition (5)(6): init(S) implies inv(S) . inv(S) implies inv(SS) .の証明譜 (Proof-inv.cafe)
 - 各invariantはinv-AAA、各wfsはwfs-BBBという述語として定義しておく。
 - (5)(6)はinvariant毎に一つずつ証明するが、証明するinvariantをinvS(S)とする。
 - Condition (5)のゴールは、initinv = init implies invS .
 - Condition (6)のゴールは、iinv = inv and invS implies invS'.とし、invinvを二重否定イディオムを使って定義する。
 - 抽象レベルで証明済みのLemmaを利用するには、具象レベルにインスタンシエートする必要があるが、現在のところ、インスタンシエーションはCafeOBJの機能を利用するように整備されていないので、手作業が必要である。

## inv-ifRSStartedThenPRReadyのCondition (5)(6)の証明譜
 - 対象invariantを設定する：invS = inv-ifRSStartedThenPRReady。
 - 一般Lemma m2o-lemma11をインスタンシエートし、「すべてのリソースがinitialならば、startedなリソースのプロパティはすべてreadyである」を言明する。Condition (5)で利用。
 - 一般Lemma m2o-lemma08をインスタンシエートし、「startedなリソースのプロパティはすべてreadyであることは、not readyプロパティがreadyに遷移しても変わらない」を言明する。Condition (6)のR02で利用。

## inv-ifRSStartedThenPRReadyのCondition (5)の証明譜
 - lemmaにより、最も一般的なケースで証明可能。

## inv-ifRSStartedThenPRReadyのR01に対するCondition (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R01のLHSを任意定数sRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initialリソースのプロパティがすべてready」なので以下の２つにケース分けする。
 - Case 1: initialリソースのプロパティがすべてready
 - Case 2: initialリソースのプロパティがすべてready、ではない => 証明可能 (次状態が無い)

### ステップ 6-3: ルール適用後の次状態がinvSになる/ならないでケース分け
 - ifRSStartedThenPRReadyは、sPRが空か否かで定義が異なる。
 - Case 1-1: sPRが空      => 証明可能 (invS(S')がtrue)
 - Case 1-2: sPRが空でない => 証明可能 (invS(S) implies invS(S')が成り立つ)

## inv-ifRSStartedThenPRReadyのR02に対するCondition (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R02のLHSを任意定数trs, idRRS, sRS, tpr, idPR, idRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R02は無条件ルールなので、ケース分けは不要。
 - Case 1: R02のLHSにマッチする最も一般的なケース => 証明可能 (invS(S) implies invS(S')が成り立つ)

## wfs-allPRHaveRSのCondition (5)(6)の証明譜
 - wfs-*はinitに含まれているのでCondition (5)の証明は不要。
 - 対象invariantを設定する：invS = wfs-allPRHaveRS。
 - 一般Lemma m2o-lemma12をインスタンシエートし、「すべてのプロパティが親リソースを持つことは、initialリソースがstartedに遷移しても変わらない」を言明する。Condition (6)のR01で利用。

## wfs-allPRHaveRSのR01に対するCondition (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R01のLHSを任意定数sRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initialリソースのプロパティがすべてready」なので以下の２つにケース分けする。
 - Case 1: initialリソースのプロパティがすべてready         => 証明可能 (lemmaによる)
 - Case 2: initialリソースのプロパティがすべてready、ではない => 証明可能 (次状態が無い)

## wfs-allPRHaveRSのR02に対するCondition (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R02のLHSを任意定数trs, idRRS, sRS, tpr, idPR, idRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R02は無条件ルールなので、ケース分けは不要。
 - Case 1: R02のLHSにマッチする最も一般的なケース => 証明可能 (invS(S) implies invS(S')が成り立つ)

## wfs-allPRHaveRRSのCondition (5)(6)の証明譜
 - wfs-*はinitに含まれているのでCondition (5)の証明は不要。
 - 対象invariantを設定する：invS = wfs-allPRHaveRRS。
 - 一般Lemma m2o-lemma12をインスタンシエートし、「すべてのプロパティが参照リソースを持つことは、initialリソースがstartedに遷移しても変わらない」を言明する。Condition (6)のR01で利用。

## wfs-allPRHaveRRSのR01に対するCondition (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R01のLHSを任意定数sRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initialリソースのプロパティがすべてready」なので以下の２つにケース分けする。
 - Case 1: initialリソースのプロパティがすべてready         => 証明可能 (lemmaによる)
 - Case 2: initialリソースのプロパティがすべてready、ではない => 証明可能 (次状態が無い)

## wfs-allPRHaveRRSのR02に対するCondition (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R02のLHSを任意定数trs, idRRS, sRS, tpr, idPR, idRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R02は無条件ルールなので、ケース分けは不要。
 - Case 1: R02のLHSにマッチする最も一般的なケース => 証明可能 (invS(S) implies invS(S')が成り立つ)

## wfs-atLeastOneRSのCondition (5)(6)の証明譜
 - wfs-*はinitに含まれているのでCondition (5)の証明は不要。
 - 対象invariantを設定する：invS = wfs-atLeastOneRS。

## wfs-atLeastOneRSのR01に対するCondition (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R01のLHSを任意定数sRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initialリソースのプロパティがすべてready」なので以下の２つにケース分けする。
 - Case 1: initialリソースのプロパティがすべてready         => 証明可能 (invS(S')がtrue)
 - Case 2: initialリソースのプロパティがすべてready、ではない => 証明可能 (次状態が無い)

## wfs-atLeastOneRSのR02に対するCondition (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R02のLHSを任意定数trs, idRRS, sRS, tpr, idPR, idRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R02は無条件ルールなので、ケース分けは不要。
 - Case 1: R02のLHSにマッチする最も一般的なケース => 証明可能 (invS(S')がtrue)

以上で、すべての十分条件が証明済みとなり、init leads-to finalが証明できた。
