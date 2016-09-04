# AWS CloudFormationのleads-to特性の検証サンプル
## CITP(Constructor-based Inductive Theorem Prover)について
### goalコマンド
 - :goal {eq EXPRESSION = true .}
 - 証明すべきゴールを設定する。

### ctfコマンド
 - :ctf {eq LHS = RHS .}
 - 「eq LHS = RHS .」と「eq (LHS = RHS) = false .」にケース分けする。

### cspコマンド
 - :csp {eq LHS1 = RHS1 . eq LHS2 = RHS2 . ...}
 - 「eq LHS1 = RHS1 .」「 eq LHS2 = RHS2 .」...にケース分けする。

### initコマンド
 - :init [LABEL] by { 変数置換 }
 - LABELを名前とする未実行(nonexec)lemmaを、変数置換して導入する。
 - 他の方法で証明済のlemmaを、ケース分けしないで導入する方法。

### applyコマンド
 - :apply (rd)
 - 現在選択中のケースでゴールをreduceする。証明できたら次のケースを選択する。

### show proofコマンド
 - show proof
 - その時点までの証明木を表示する。証明済のケースには*が示される。

## CITPテクニック
### テクニック (1)
 - CITPではgoalを途中で変更できないので、「AならばB」の形式のLemmaを導入する場合は、eq (A implies B) = true.を定義するが、以下のいずれかの方がこれと等価で効率が良い。
   1. ceq B = true if A .　　　
   2. ceq A = false if not B .
   3. eq (A and B) = A .

 - i.はLemmaを後件に利用する場合に適している。ii.は前件に利用する場合に適している。ただし、条件節に置く式の方が変数がすべて左辺に置く式に現れていなければならない。
 - iii.は「A implies B」と「(A and B) = A」が等価であることを利用する方法であり直感的にわかりにくいものの、前件にも後件にも利用できること、AとBに含まれる変数の包含関係に気にしないで利用できること、という利点がある。

### テクニック (2)
 - 任意定数をさらに詳細化した場合に、定義済みの等式が成立しなくなることがある。
 - すでに eq pred(sPR) = true .を定義済みのケースをさらに分けたときに、eq sPR = (aPR sPR') .とsPRを詳細化することがある。
 - 「pred(sPR)」を外側から評価すればtrueになるが、引数のsPRから先に評価した場合にpredの定義によってtrueにならないことがある。
 - そこで、「もしpred(sPR)がtrueにならないならばtrueである」というlemmaを以下のように導入しておく。
   - :init ( ceq B1 = true if not B2 . ) by { B1 <- pred(sPR) ; B2 <- pred(sPR) == true ; }
 - 「:set(normalize-init,on)」を指定すると、変数置換の前に置換式を評価するので、pred(sPR)の評価後の式がなんであれtrueであることを表明できる。
  - pred(sPR)の評価がtrueの場合は、ceq true = true if not true .となって影響が無い。

## 証明の準備　(Proof.cafe)
### invariantとwell-formed stateの準備
 - 各invariantはinv-AAA、各wfsはwfs-BBBという述語として定義しておく。
 - condition (1)(2)(3)(4)の証明に対してはCITPテクニック(1)を使って、あらかじめ以下の定義を与えておく。
   - eq inv(S) = false if not inv-AAA(S) .
   - eq wfs(S) = false if not wfs-BBB(S) .

### Cyclic Dependency Lemma(CDL)適用の準備
 - 「状態Sで、あるinitialリソースのDDSに、別のinitialリソースが含まれたら、矛盾する」という未実行(nonexec)lemma CycleR01を定義しておく。
 - CycleR01を適用するinitialリソースを導入するためのスコーレム関数を２つ(そのリソースと残り)用意しておく。
 - CDL適用可能な状態に対して、スコーレム関数を適用して対象リソースを導入し、initコマンドで矛盾lemmaを導入する。

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
 - 用意しておいたCycleR01未実行lemmaを、このinitialリソースを対象として導入する。
 - このリソースのDDSに、referリンクの参照先リソースが含まれるので、矛盾が生じ、証明が完了する。

## Condtion (2): inv(S) and not final(S) implies cont(SS) or final(SS) の証明譜 (Proof-contcont.cafe)
### ステップ 2-0: 証明すべき述語を定義
 - ccont = wfs and inv and not final implies cont' or final'
 - wfsを、invと区別して定義しているので前件に加えておく。
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
 - 用意しておいたCycleR01未実行lemmaを、このinitialリソースを対象として導入する。
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
 - スコーレム関数を利用してsRS'を分解し、CDL適用対象リソースidRS1を導入する。

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
 - mmes = wfs and inv and not final implies m > m'
 - wfsを、invと区別して定義しているので前件に加えておく。
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
 - mesfinal = wfs and inv and (cont or final) and m = 0 implies final .
 - wfsを、invと区別して定義しているので前件に加えておく。

### ステップ 4-1: m(S)用の一般Lemmaをインスタンシエート
 - initialリソースの数が0ならば、すべてのリソースはstartedである。

### ステップ 4-2: 自然数に対するAxiomを定義
 - 「N1 + N2 = 0」と「N1 = 0 かつ N2 = 2」が等価である。

## Condtion (5)(6): init(S) implies inv(S) . inv(S) implies inv(SS) .の証明譜 (Proof-inv.cafe)
 - 各invariantはinv-AAA、各wfsはwfs-BBBという述語として定義しておく。
 - Condition (1)(2)(3)(4)の証明に対してはCITPテクニック(1)を使ってすべてのinv-AAAとwfs-BBBを有効にしておく。
 - Condition (5)(6)の証明に際しては、invariant間に依存関係があるので注意が必要。
   - (5)(6)はinvariant毎に一つずつ証明するが、証明するinvariantをinvS(S)とし、依存する（証明済みの）invariantをCITPテクニック(1)を使って有効にしておく。
   - Condition (5)のゴールは、initinv = init implies invS .
   - Condition (6)のゴールは、iinv = wfs and inv and invS implies invS'.とし、invinvを二重否定イディオムを使って定義する。
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
 - wfsはinitに含まれているのでCondition (5)の証明は不要。
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
 - wfsはinitに含まれているのでCondition (5)の証明は不要。
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
 - wfsはinitに含まれているのでCondition (5)の証明は不要。
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
