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

## Preparation of Proof
### Step 0-1: Define `init(S)` and `final(S)`.
 - Among conditions explicitly composing init(S), one referring to no local states of objects and being expected to be an invariant is called a wfs (well-formed state).
 - Define `wfs(S)` as a conjunction of all wfs's.

  ```Domain.cafe
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

### Step 0-2: Define `cont(S)`.
 - Define `cont(S)` as follows using the unconditional search predicate.

  ```Proof.cafe
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
 - Prepare a nonexec lemma which means that `DDS` of a specified initial resource never includs other initial resources.

  ```
  ceq [Cycle :nonexec]: 
     true = false if someRSInStates(DDSC(res(T, IDRS, initial),S),initial) .
  ```

## Condtion (1): init(S) implies cont(S) の証明譜 (Proof-initcont.cafe)
### ステップ 1-0: 証明すべき述語を定義
 - initcont = init implies cont

### ステップ 1-1: 最も一般的なケースから開始
 - 任意定数sRS(リソースの集合)、sPR(プロパティの集合)により、最も一般的な状態は< sRS, sPR >。

### ステップ 1-2: 初期状態で最初に適用されるルールを考察
 - 最初のルールはR01。

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R01のLHSは１つ以上のinitialリソースが必要なので、cspコマンドで以下の３つにケース分けする。
 - Case 1: リソースが一つもない => 証明可能 (init(S)がfalse)
 - Case 2-1: initialリソースが少なくとも一つある
 - Case 2-2: startedリソースが少なくとも一つある => 証明可能 (init(S)がfalse)

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initialリソースのプロパティがすべてready」なので以下の２つにケース分けする。
 - Case 2-1-1: initialリソースのプロパティがすべてready => 証明可能 (R01が適用可能)
 - Case 2-1-2: initialリソースのプロパティのうちnotreadyなものが少なくとも一つある

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - notreadyプロパティのreferリンクが未定なので、以下の３つにケース分けする
 - Case 2-1-2-1: referリンクの参照先が存在しない => 証明可能 (wfs-allPRHaveRRS(S)がfalse)
 - Case 2-1-2-2-1: referリンクの参照先リソースが存在してinitial
 - Case 2-1-2-2-2: referリンクの参照先リソースが存在してstarted => 証明可能 (init(S)がfalse)

### ステップ 1-6: 循環する状況になったらCyclic Dependency Lemmaを適用
 - ここでCase 2-1には、任意に選択したinitialリソースがあるので、これをCDL適用対象と考えて良い (新規に導入不要)。
 - 用意しておいたCycle未実行lemmaを、このinitialリソースを対象として導入する。
 - このリソースのDDSに、referリンクの参照先リソースが含まれるので、矛盾が生じ、証明が完了する。

## Condtion (2): inv(S) and not final(S) implies cont(SS) or final(SS) の証明譜 (Proof-contcont.cafe)
### ステップ 2-0: 証明すべき述語を定義
 - ccont = inv and not final implies cont' or final'
 - 次状態が存在する状態に関する条件なので、前件にcont(S)が不要であることに注意。
 - contcontを二重否定イディオムを使って定義する。

## R01に対するCondtion (2)の証明譜 (Proof-contcont-R01.cafe)
### ステップ 2-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R01のLHSは１つ以上のinitialリソースが必要なので、trs, idRS, sRS, sPRを任意定数として< (res(trs,idRS,initial) sRS), sPR >が最も一般的な状態。

### ステップ 2-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initialリソースのプロパティがすべてready」なので以下の２つにケース分けする。
 - Case 1: initialリソースのプロパティがすべてready
 - Case 2: initialリソースのプロパティがすべてready、ではない => 証明可能 (次状態が無い)

### ステップ 2-3: ルール適用後の次状態がfinalになる/ならないでケース分け
 - R01適用後にはstartedリソースが一つあるので、残りのリソースが全部startedならfinalになる。そこで、以下の２つにケース分けする。
 - Case 1-1: 残りのリソースすべてがstarted => 証明可能 (final(S')がtrue)
 - Case 1-2: 残りのリソースの少なくとも一つがinitial

### ステップ 2-4: 次状態に適用されるルールを考察
 - initialリソースがあるので、適用されるルールはR01。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initialリソースのプロパティがすべてready」なので以下の２つにケース分けする。
 - Case 1-2-1: initialリソースのプロパティがすべてready => 証明可能 (次状態にR01が適用可能)
 - Case 1-2-2: initialリソースのプロパティのうちnotreadyなものが少なくとも一つある

### CITPテクニック(2)を使って、sPRの詳細化に対してallPROfRSInStates(sPR,idRS,ready)がtrueになることを保証しておく。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - notreadyプロパティのreferリンクが未定なので、以下の３つにケース分けする
 - Case 1-2-2-1: referリンクの参照先が存在しない => 証明可能 (wfs-allPRHaveRRS(S)がfalse)
 - Case 1-2-2-2-1: referリンクの参照先リソースが存在してinitial
 - Case 1-2-2-2-2: referリンクの参照先リソースが存在してstarted => 証明可能 (次状態にR02が適用可能)

### ステップ 2-5: 循環する状況になったらCyclic Dependency Lemmaを適用
 - Case 1-2には、任意に選択したinitialリソースがあるので、これをCDL適用対象と考えて良い (新規に導入不要)。
 - 用意しておいたCycle未実行lemmaを、このinitialリソースを対象として導入する。
 - このリソースのDDSに、referリンクの参照先リソースが含まれるので、矛盾が生じ、証明が完了する。

## R02に対するCondtion (2)の証明譜 (Proof-contcont-R02.cafe)
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

## Condtion (3): inv(S) and not final(S) implies m(S) > m(SS) の証明譜 (Proof-measure.cafe)
### ステップ 3-0: 証明すべき述語を定義
 - mmes = inv and not final implies m > m'
 - 次状態が存在する状態に関する条件なので、前件にcont(S)が不要であることに注意。
 - mesmesを二重否定イディオムを使って定義する。
 - 自然数に対するAxiomとして N < N+1 を定義しておく。

## R01に対するCondtion (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R01のLHSを任意定数trs, idRS, sRS, sPRで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initialリソースのプロパティがすべてready」なので以下の２つにケース分けする。
 - Case 1: initialリソースのプロパティがすべてready => 証明可能 (m(S) > m(SS)が成り立つ)
 - Case 2: initialリソースのプロパティがすべてready、ではない => 証明可能 (次状態が無い)

## R02に対するCondtion (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R02のLHSを任意定数trs, idRRS, sRS, tpr, idPR, idRS, sPRで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R02は無条件ルールなので、ケース分けは不要。
 - Case 1: R02のLHSにマッチする最も一般的なケース => 証明可能 (m(S) > m(SS)が成り立つ)

## Condtion (4): inv(S) and (cont(S) or final(S)) and m(S) = 0 implies final(S) の証明譜 (Proof-measure.cafe)
### ステップ 4-0: 証明すべき述語を定義
 - mesfinal = inv and (cont or final) and m = 0 implies final .

### ステップ 4-1: m(S)用の一般Lemmaをインスタンシエート
 - initialリソースの数が0ならば、すべてのリソースはstartedである。

### ステップ 4-2: 自然数に対するAxiomを定義
 - 「N1 + N2 = 0」と「N1 = 0 かつ N2 = 2」が等価である。

## Condtion (5)(6): init(S) implies inv(S) . inv(S) implies inv(SS) .の証明譜 (Proof-inv.cafe)
 - 各invariantはinv-AAA、各wfsはwfs-BBBという述語として定義しておく。
 - (5)(6)はinvariant毎に一つずつ証明するが、証明するinvariantをinvS(S)とする。
 - Condition (5)のゴールは、initinv = init implies invS .
 - Condition (6)のゴールは、iinv = inv and invS implies invS'.とし、invinvを二重否定イディオムを使って定義する。
 - 抽象レベルで証明済みのLemmaを利用するには、具象レベルにインスタンシエートする必要があるが、現在のところ、インスタンシエーションはCafeOBJの機能を利用するように整備されていないので、手作業が必要である。

## inv-ifRSStartedThenPRReadyのCondtion (5)(6)の証明譜
 - 対象invariantを設定する：invS = inv-ifRSStartedThenPRReady。
 - 一般Lemma m2o-lemma11をインスタンシエートし、「すべてのリソースがinitialならば、startedなリソースのプロパティはすべてreadyである」を言明する。Condtion (5)で利用。
 - 一般Lemma m2o-lemma08をインスタンシエートし、「startedなリソースのプロパティはすべてreadyであることは、not readyプロパティがreadyに遷移しても変わらない」を言明する。Condtion (6)のR02で利用。

## inv-ifRSStartedThenPRReadyのCondtion (5)の証明譜
 - lemmaにより、最も一般的なケースで証明可能。

## inv-ifRSStartedThenPRReadyのR01に対するCondtion (6)の証明譜
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

## inv-ifRSStartedThenPRReadyのR02に対するCondtion (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R02のLHSを任意定数trs, idRRS, sRS, tpr, idPR, idRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R02は無条件ルールなので、ケース分けは不要。
 - Case 1: R02のLHSにマッチする最も一般的なケース => 証明可能 (invS(S) implies invS(S')が成り立つ)

## wfs-allPRHaveRSのCondtion (5)(6)の証明譜
 - wfs-*はinitに含まれているのでCondition (5)の証明は不要。
 - 対象invariantを設定する：invS = wfs-allPRHaveRS。
 - 一般Lemma m2o-lemma12をインスタンシエートし、「すべてのプロパティが親リソースを持つことは、initialリソースがstartedに遷移しても変わらない」を言明する。Condtion (6)のR01で利用。

## wfs-allPRHaveRSのR01に対するCondtion (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R01のLHSを任意定数sRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initialリソースのプロパティがすべてready」なので以下の２つにケース分けする。
 - Case 1: initialリソースのプロパティがすべてready         => 証明可能 (lemmaによる)
 - Case 2: initialリソースのプロパティがすべてready、ではない => 証明可能 (次状態が無い)

## wfs-allPRHaveRSのR02に対するCondtion (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R02のLHSを任意定数trs, idRRS, sRS, tpr, idPR, idRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R02は無条件ルールなので、ケース分けは不要。
 - Case 1: R02のLHSにマッチする最も一般的なケース => 証明可能 (invS(S) implies invS(S')が成り立つ)

## wfs-allPRHaveRRSのCondtion (5)(6)の証明譜
 - wfs-*はinitに含まれているのでCondition (5)の証明は不要。
 - 対象invariantを設定する：invS = wfs-allPRHaveRRS。
 - 一般Lemma m2o-lemma12をインスタンシエートし、「すべてのプロパティが参照リソースを持つことは、initialリソースがstartedに遷移しても変わらない」を言明する。Condtion (6)のR01で利用。

## wfs-allPRHaveRRSのR01に対するCondtion (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R01のLHSを任意定数sRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initialリソースのプロパティがすべてready」なので以下の２つにケース分けする。
 - Case 1: initialリソースのプロパティがすべてready         => 証明可能 (lemmaによる)
 - Case 2: initialリソースのプロパティがすべてready、ではない => 証明可能 (次状態が無い)

## wfs-allPRHaveRRSのR02に対するCondtion (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R02のLHSを任意定数trs, idRRS, sRS, tpr, idPR, idRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R02は無条件ルールなので、ケース分けは不要。
 - Case 1: R02のLHSにマッチする最も一般的なケース => 証明可能 (invS(S) implies invS(S')が成り立つ)

## wfs-atLeastOneRSのCondtion (5)(6)の証明譜
 - wfs-*はinitに含まれているのでCondition (5)の証明は不要。
 - 対象invariantを設定する：invS = wfs-atLeastOneRS。

## wfs-atLeastOneRSのR01に対するCondtion (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R01のLHSを任意定数sRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initialリソースのプロパティがすべてready」なので以下の２つにケース分けする。
 - Case 1: initialリソースのプロパティがすべてready         => 証明可能 (invS(S')がtrue)
 - Case 2: initialリソースのプロパティがすべてready、ではない => 証明可能 (次状態が無い)

## wfs-atLeastOneRSのR02に対するCondtion (6)の証明譜
### ステップ 6-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R02のLHSを任意定数trs, idRRS, sRS, tpr, idPR, idRS, sPRで表現する。

### ステップ 6-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R02は無条件ルールなので、ケース分けは不要。
 - Case 1: R02のLHSにマッチする最も一般的なケース => 証明可能 (invS(S')がtrue)

以上で、すべての十分条件が証明済みとなり、init leads-to finalが証明できた。
