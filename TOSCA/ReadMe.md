# OASIS TOSCAのleads-to特性の検証サンプル
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
 - wfs(well-formed state)とは、invariantの内でinitに現れるものである。wfsについてはcondition (5)の証明は不要。（以下、invariantとはwfsではないinvariantのこと）
 - 各invariantはinv-AAA、各wfsはwfs-BBBという述語として定義しておく。
 - condition (1)(2)(3)(4)の証明に対してはCITPテクニック(1)を使って、あらかじめ以下の定義を与えておく。
   - eq inv(S) = false if not inv-AAA(S) .
   - eq wfs(S) = false if not wfs-BBB(S) .

### Cyclic Dependency Lemma(CDL)適用の準備
#### R01に対して
 - 「状態Sで、あるinitial nodeのDDSに、別のinitial nodeが含まれたら、矛盾する」という未実行(nonexec)lemma CycleR01を定義しておく。
 - CycleR01を適用するinitial nodeを導入するためのスコーレム関数を用意しておく。
 - CDL適用可能な状態に対して、スコーレム関数を適用して対象nodeを導入し、initコマンドでCycleR01を導入し、矛盾を導く。
 - 「initial nodeが存在すれば適用可能なルールが存在する、つまりcont(S)が成り立つ」ことはcondition (1)と(2)の多くのルールの証明で度々必要になるので、Initial Cont Lemmaとして事前に証明しておく(Proof-cyclelemma.cafe)。証明内容については後述。

#### R02に対して
 - 「状態Sで、あるcreated nodeのDDSに、別のcreated nodeが含まれたら、矛盾する」という未実行(nonexec)lemma CycleR02を定義しておく。
 - CycleR02を適用するcreated nodeを導入するためのスコーレム関数を用意しておく。
 - CDL適用可能な状態に対して、スコーレム関数を適用して対象nodeを導入し、initコマンドでCycleR02を導入し、矛盾を導く。
 - 「created nodeが存在すれば適用可能なルールが存在する、つまりcont(S)が成り立つ」ことはcondition (1)と(2)の多くのルールの証明で度々必要になるので、Created Cont Lemmaとして事前に証明しておく(Proof-cyclelemma.cafe)。証明内容については後述。

## Condtion (1): init(S) implies cont(S) の証明譜 (Proof-initcont.cafe)
### ステップ 1-0: 証明すべき述語を定義
 - initcont = init implies cont
 - Initial Cont Lemmaを導入し、initial nodeがあればcont(S)はtrueになることを表明しておく。

### ステップ 1-1: 最も一般的なケースから開始
 - 任意定数sND(nodeの集合)、sCP(Capabilityの集合)、sRQ(Requirementの集合)、sRL(Relationshipの集合)、mp(メッセージプール)により、最も一般的な状態は< sND, sCP, sRQ, sRL, mp >。

### ステップ 1-2: 初期状態で最初に適用されるルールを考察
 - 最初のルールはR01。

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R01のLHSは１つ以上のinitial nodeが必要なので、cspコマンドで以下の３つにケース分けする。
 - Case 1: nodeが一つもない => 証明可能 (init(S)がfalse)
 - Case 2-1: initial nodeが少なくとも一つある => 証明可能 (Initial Cont Lemmaによりcont(S)がtrue)
 - Case 2-2: created nodeが少なくとも一つある => 証明可能 (init(S)がfalse)
 - Case 2-3: started nodeが少なくとも一つある => 証明可能 (init(S)がfalse)

## Condtion (2): inv(S) and not final(S) implies cont(SS) or final(SS) の証明譜 (Proof-contcont.cafe)
### ステップ 2-0: 証明すべき述語を定義
 - ccont = wfs and inv and not final implies cont' or final'
 - wfsを、invと区別して定義しているので前件に加えておく。
 - 次状態が存在する状態に関する条件なので、前件にcont(S)が不要であることに注意。
 - contcontを二重否定イディオムを使って定義する。
 - Initial Cont Lemmaを導入し、initial nodeがあればcont(S)はtrueになることを表明しておく。
 - Created Cont Lemmaを導入し、created nodeがあればcont(S)はtrueになることを表明しておく。

## R01に対するCondtion (2)の証明譜 (Proof-contcont-R01.cafe)
### ステップ 2-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R01のLHSは１つ以上のinitial nodeが必要なので、tnd, idND, sND, sCP, sRQ, sRL,mpを任意定数として< (node(tnd,idND,initial) sND), sCP, sRQ, sRL, mp >が最も一般的な状態。

### ステップ 2-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initial nodeのhostedOn requirementがすべてready」なので以下の２つにケース分けする。
 - Case 1: initial nodeのhostedOn requirementがすべてready => 証明可能 (Created Cont Lemmaによりcont(S')がtrue)
 - Case 2: initial nodeのhostedOn requirementがすべてready、ではない => 証明可能 (次状態が無い)

## R02に対するCondtion (2)の証明譜 (Proof-contcont-R02.cafe)
### ステップ 2-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R02のLHSは１つ以上のcreated nodeが必要なので、tnd, idND, sND, sCP, sRQ, sRL,mpを任意定数として< (node(tnd,idND,created) sND), sCP, sRQ, sRL, mp >が最も一般的な状態。

### ステップ 2-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R02の条件節は「created nodeのrequirementがすべてready」なので以下の２つにケース分けする。
 - Case 1: created nodeのrequirementがすべてready
 - Case 2: created nodeのrequirementがすべてready、ではない => 証明可能 (次状態が無い)

### ステップ 2-3: ルール適用後の次状態がfinalになる/ならないでケース分け
 - R02適用後にはstarted nodeが一つあるので、残りのnodeが全部startedならfinalになる。そこで、以下の２つにケース分けする。
 - Case 1-1: 残りのnodeすべてがstarted => 証明可能 (final(S')がtrue)
 - Case 1-2: 残りのnodeの少なくとも一つがinitial => 証明可能 (Initial Cont Lemmaによりcont(S')がtrue)
 - Case 1-3: 残りのnodeの少なくとも一つがcreated => 証明可能 (Created Cont Lemmaによりcont(S')がtrue)

## R03に対するCondtion (2)の証明譜 (Proof-contcont-R03.cafe)
### ステップ 2-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R03のLHSは１つ以上のclosedなhostedOn capabilityが必要なので、< sND, (cap(hostedOn,idCP,closed,idND) sCP), sRQ, sRL, mp >が最も一般的な状態。

### ステップ 2-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R03の条件節は「closed capabilityの親nodeがisCreated」なので以下の２つにケース分けする。
 - Case 1: closed capabilityの親nodeがisCreated
 - Case 2: closed capabilityの親nodeがisCreated、ではない => 証明可能 (次状態が無い)

### ステップ 2-3: ルール適用後の次状態がfinalになる/ならないでケース分け
 - R03適用直後にfinalにならないことはわかっている。

### ステップ 2-4: 次状態に適用されるルールを考察
 - availableなhostedOn capabilityがあるので、適用されるルールはR04。

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R04のLHSはavailable capabilityに対応するrelationshipと、さらにそれに対応するunbound requirementが必要なので、以下のようにケース分けする。
 - Case 1-1: 対応するrelationshipが無い => 証明可能 (wfs-allCPHaveRL(S)がfalse)
 - Case 1-2: 対応するrelationshipがある
   - Case 1-2-1: 対応するrelationshipがhostedOn
     - Case 1-2-1-1: 対応するrequirementが無い => 証明可能 (wfs-allRLHaveRQ(S)がfalse)
     - Case 1-2-1-2: 対応するrequirementがある
　　　　 - Case 1-2-1-2-1: 対応するrequirementがhostedOn
  　　　　 - Case 1-2-1-2-1-1: 対応するrequirementがunbound => 証明可能 (R04が適用可能なのでcont(S')がtrue)
  　　　　 - Case 1-2-1-2-1-2: 対応するrequirementがwaiting => 証明可能 (inv-ifCPClosedThenRQUnbound(S)がfalse)
　  　　　 - Case 1-2-1-2-1-3: 対応するrequirementがready => 証明可能 (inv-ifCPClosedThenRQUnbound(S)がfalse)

　　　　 - Case 1-2-1-2-2: 対応するrequirementがdependsOn => 証明可能 (wfs-allRLHaveSameTypeCPRQ(S)がfalse)
　　　　 - Case 1-2-1-2-3: 対応するrequirementがconnectsTo => 証明可能 (wfs-allRLHaveSameTypeCPRQ(S)がfalse)

   - Case 1-2-2: 対応するrelationshipがdependsOn => 証明可能 (wfs-allRLHaveSameTypeCPRQ(S)がfalse)
   - Case 1-2-3: 対応するrelationshipがconnectsTo => 証明可能 (wfs-allRLHaveSameTypeCPRQ(S)がfalse)

## R04に対するCondtion (2)の証明譜 (Proof-contcont-R04.cafe)
### ステップ 2-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R04のLHSはavailable capability、それに対応するrelationshipと、されにそれに対応するunbound requirementが必要なので、< sND, (cap(hostedOn,idCP,available,idND) sCP), (req(hostedOn,idRQ,unbound,idND') sRQ), (rel(hostedOn,idRL,idCP,idRQ) sRL), mp >が最も一般的な状態。

### ステップ 2-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R04は無条件ルール。

### ステップ 2-3: ルール適用後の次状態がfinalになる/ならないでケース分け
 - R03適用直後にfinalにならないことはわかっている。

### ステップ 2-4: 次状態に適用されるルールを考察
 - readyなhostedOn requirementがあるので、適用されるルールはR01。

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R01のLHSはready requirementに対応するinitial nodeが必要なので、以下のようにケース分けする。
 - Case 1: 対応するnodeが無い => 証明可能 (wfs-allRQHaveND(S)がfalse)
 - Case 2: 対応するnodeがある
   - Case 2-1: 対応するnodeがinitial => 証明可能 (Initial Cont Lemmaによりcont(S')がtrue)
   - Case 2-2: 対応するnodeがcreated => 証明可能 (inv-ifNDCreatedThenHostedOnRQReady(S)がfalse)
   - Case 2-2: 対応するnodeがstarted => 証明可能 (inv-ifNDStartedThenRQReady(S)がfalse)

## R05に対するCondtion (2)の証明譜 (Proof-contcont-R05.cafe)
### ステップ 2-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R05のLHSは１つ以上のclosedなdependsOn capabilityが必要なので、< sND, (cap(dependsOn,idCP,closed,idND) sCP), sRQ, sRL, mp >が最も一般的な状態。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親nodeのリンクが未定なので、以下の２つにケース分けする
 - Case 1: 対応するnodeが無い => 証明可能 (wfs-allCPHaveND(S)がfalse)
 - Case 2: 対応するnodeがある

### ステップ 2-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R05の条件節は「closed capabilityの親nodeがisCreated」なので以下の３つにケース分け。
 - Case 2-1: capabilityに対応するnodeがinitial => 証明可能 (Initial Cont Lemmaによりcont(S')がtrue)
 - Case 2-2: capabilityに対応するnodeがcreated => 証明可能 (Created Cont Lemmaによりcont(S')がtrue)
 - Case 2-3: capabilityに対応するnodeがstarted => 証明可能 (R06が適用可能なのでcont(S')がtrue)

## R06に対するCondtion (2)の証明譜 (Proof-contcont-R06.cafe)
### ステップ 2-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R06のLHSは１つ以上のopenなdependsOn capabilityが必要なので、< sND, (cap(dependsOn,idCP,open,idND) sCP), sRQ, sRL, mp >が最も一般的な状態。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親nodeのリンクが未定なので、以下の２つにケース分けする
 - Case 1: 対応するnodeが無い => 証明可能 (wfs-allCPHaveND(S)がfalse)
 - Case 2: 対応するnodeがある

### ステップ 2-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R06の条件節は「closed capabilityの親nodeがisCreated」なので以下の３つにケース分け。
 - Case 2-1: capabilityに対応するnodeがinitial => 証明可能 (Initial Cont Lemmaによりcont(S')がtrue)
 - Case 2-2: capabilityに対応するnodeがcreated => 証明可能 (Created Cont Lemmaによりcont(S')がtrue)
 - Case 2-3: capabilityに対応するnodeがstarted

### ステップ 2-3: ルール適用後の次状態がfinalになる/ならないでケース分け
 - R06適用直後にfinalにならないことはわかっている。

### ステップ 2-4: 次状態に適用されるルールを考察
 - availableなdependsOn capabilityがあるので、適用されるルールはR08。

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R08のLHSはavailable capabilityに対応するrelationshipと、さらにそれに対応するwaiting requirementが必要なので、以下のようにケース分けする。
 - Case 2-3-1: 対応するrelationshipが無い => 証明可能 (wfs-allCPHaveRL(S)がfalse)
 - Case 2-3-2: 対応するrelationshipがある
   - Case 2-3-2-1: 対応するrelationshipがhostedOn => 証明可能 (wfs-allRLHaveSameTypeCPRQがfalse)
   - Case 2-3-2-2: 対応するrelationshipがdependsOn => 証明可能 (wfs-allRLHaveSameTypeCPRQ(S)がfalse)
   - Case 2-3-2-3: 対応するrelationshipがconnectsTo
     - Case 2-3-2-3-1: 対応するrequirementが無い => 証明可能 (wfs-allRLHaveRQ(S)(S)がfalse)
     - Case 2-3-2-3-2: 対応するrequirementがある
　　　　 - Case 2-3-2-3-2-1: 対応するrequirementがhostedOn => 証明可能 (wfs-allRLHaveSameTypeCPRQ(S)がfalse)
　　　　 - Case 2-3-2-3-2-2: 対応するrequirementがdependsOn => 証明可能 (wfs-allRLHaveSameTypeCPRQ(S)がfalse)
　　　　 - Case 2-3-2-3-2-3: 対応するrequirementがconnectsTo
  　　　　 - Case 2-3-2-3-2-3-1: 対応するrequirementがunbound
  　　　　 - Case 2-3-2-3-2-3-2: 対応するrequirementがwaiting => 証明可能 (R08が適用可能なのでcont(S')がfalse)
　  　　　 - Case 2-3-2-3-2-3-3: 対応するrequirementがready => 証明可能 (inv-ifCPClosedThenRQUnbound(S)がfalse)


   - ここでCase 2-3-2-3-2-3-1がまだ残っている。

### ステップ 2-4: 次状態に適用されるルールを考察
 - unboundなconnectsTo requirementがあるので、適用されるルールはR11。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R11の条件節は「unbound requiremetのnodeがcreated、かつcapabilityがisActivated」だが、capabilityはopenなので、nodeの条件で以下の3つにケース分けする。
 - Case 2-3-2-3-2-3-1-2-1: unbound requiremetのnodeがinitial => 証明可能 (Initial Cont Lemmaによりconst(S')がtrue)
 - Case 2-3-2-3-2-3-1-2-2: unbound requiremetのnodeがcreated => 証明可能 (R07が適用可能なのでcont(S')がtrue)
 - Case 2-3-2-3-2-3-1-2-3: unbound requiremetのnodeがstarted => 証明可能 (inv-ifCPOpenThenRQUnboundWaiting(S)がfalse)

## R07に対するCondtion (2)の証明譜 (Proof-contcont-R07.cafe)
### ステップ 2-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R07のLHSはunbound requirementに対応するrelationshipと、さらにそれに対応するcapabilityが必要なので、< sND, (cap(dependsOn,idCP,scp,idND) sCP), (req(dependsOn,idRQ,unbound,idND') sRQ), (rel(dependsOn,idRL,idCP,idRQ) sRL), mp >が最も一般的な状態。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - requirementの親nodeのリンクが未定なので、以下の２つにケース分けする
 - Case 1: 対応するnodeが無い => 証明可能 (wfs-allRQHaveND(S)がfalse)
 - Case 2: 対応するnodeがある

### ステップ 2-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R07の条件節は「unbound requiremetのnodeがcreated、かつcapabilityがisActivated」なので、まずはnodeの状態について以下の３つにケース分け。
 - Case 2-1: requirementに対応するnodeがinitial => 証明可能 (Initial Cont Lemmaによりcont(S')がtrue)
 - Case 2-2: requirementに対応するnodeがcreated => 証明可能 (Created Cont Lemmaによりcont(S')がtrue)
 - Case 2-3: requirementに対応するnodeがstarted => 証明可能 (次状態が無い)

## R08に対するCondtion (2)の証明譜 (Proof-contcont-R08.cafe)
### ステップ 2-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R08のLHSはwaiting requirementに対応するrelationshipと、さらにそれに対応するavailable capabilityが必要なので、< sND, (cap(dependsOn,idCP,available,idND) sCP), (req(dependsOn,idRQ,waiting,idND') sRQ), (rel(dependsOn,idRL,idCP,idRQ) sRL), mp >が最も一般的な状態。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - requirementの親nodeのリンクが未定なので、以下の２つにケース分けする
 - Case 1: 対応するnodeが無い => 証明可能 (wfs-allRQHaveND(S)がfalse)
 - Case 2: 対応するnodeがある

### ステップ 2-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R08は無条件ルール。

### ステップ 2-3: ルール適用後の次状態がfinalになる/ならないでケース分け
 - R08適用直後にfinalにならないことはわかっている。

### ステップ 2-4: 次状態に適用されるルールを考察
 - readyなrequirementがあるので、適用されるルールはR02。

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R02のLHSはrequiremntに対応するcreated nodeが必要なので、cspコマンドで以下の３つにケース分けする。
 - Case 2-1: requirementに対応するnodeがinitial => 証明可能 (inv-ifNDInitialThenRQUnboundReady(S)がfalse)
 - Case 2-2: requirementに対応するnodeがcreated => 証明可能 (R02が適用可能なのでcont(S')がtrue)
 - Case 2-3: requirementに対応するnodeがstarted => 証明可能 (inv-ifNDStartedThenRQReady(S)がfalse)

## R09に対するCondtion (2)の証明譜 (Proof-contcont-R09.cafe)
### ステップ 2-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R09のLHSは１つ以上のclosedなconnectsTo capabilityが必要なので、< sND, (cap(connectsTo,idCP,closed,idND) sCP), sRQ, sRL, mp >が最も一般的な状態。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親nodeのリンクが未定なので、以下の２つにケース分けする
 - Case 1: 対応するnodeが無い => 証明可能 (wfs-allCPHaveND(S)がfalse)
 - Case 2: 対応するnodeがある

### ステップ 2-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R09の条件節は「closed capabilityの親nodeがisCreated」なので以下の３つにケース分け。
 - Case 2-1: capabilityに対応するnodeがinitial => 証明可能 (Initial Cont Lemmaによりcont(S')がtrue)
 - Case 2-2: capabilityに対応するnodeがcreated => 証明可能 (Created Cont Lemmaによりcont(S')がtrue)
 - Case 2-3: capabilityに対応するnodeがstarted => 証明可能 (R10が適用可能なのでcont(S')がtrue)

## R10に対するCondtion (2)の証明譜 (Proof-contcont-R10.cafe)
### ステップ 2-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R10のLHSは１つ以上のopenなconnectsTo capabilityが必要なので、< sND, (cap(connectsTo,idCP,open,idND) sCP), sRQ, sRL, mp >が最も一般的な状態。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親nodeのリンクが未定なので、以下の２つにケース分けする
 - Case 1: 対応するnodeが無い => 証明可能 (wfs-allCPHaveND(S)がfalse)
 - Case 2: 対応するnodeがある

### ステップ 2-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R10の条件節は「closed capabilityの親nodeがisCreated」なので以下の３つにケース分け。
 - Case 2-1: capabilityに対応するnodeがinitial => 証明可能 (Initial Cont Lemmaによりcont(S')がtrue)
 - Case 2-2: capabilityに対応するnodeがcreated => 証明可能 (Created Cont Lemmaによりcont(S')がtrue)
 - Case 2-3: capabilityに対応するnodeがstarted

### ステップ 2-3: ルール適用後の次状態がfinalになる/ならないでケース分け
 - R10適用直後にfinalにならないことはわかっている。

### ステップ 2-4: 次状態に適用されるルールを考察
 - availableなconnectsTo capabilityがあるので、適用されるルールはR12。

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R12のLHSはavailable capabilityに対応するrelationshipと、さらにそれに対応するwaiting requirementが必要なので、以下のようにケース分けする。
 - Case 2-3-1: 対応するrelationshipが無い => 証明可能 (wfs-allCPHaveRL(S)がfalse)
 - Case 2-3-2: 対応するrelationshipがある
   - Case 2-3-2-1: 対応するrelationshipがhostedOn => 証明可能 (wfs-allRLHaveSameTypeCPRQがfalse)
   - Case 2-3-2-3: 対応するrelationshipがdependsOn
     - Case 2-3-2-3-1: 対応するrequirementが無い => 証明可能 (wfs-allRLHaveRQ(S)(S)がfalse)
     - Case 2-3-2-3-2: 対応するrequirementがある
　　　　 - Case 2-3-2-3-2-1: 対応するrequirementがhostedOn => 証明可能 (wfs-allRLHaveSameTypeCPRQ(S)がfalse)
　　　　 - Case 2-3-2-3-2-3: 対応するrequirementがdependsOn
  　　　　 - Case 2-3-2-3-2-3-1: 対応するrequirementがunbound
  　　　　 - Case 2-3-2-3-2-3-2: 対応するrequirementがwaiting => 証明可能 (R12が適用可能なのでcont(S')がfalse)
　  　　　 - Case 2-3-2-3-2-3-3: 対応するrequirementがready => 証明可能 (inv-ifCPClosedThenRQUnbound(S)がfalse)

　　　　 - Case 2-3-2-3-2-3: 対応するrequirementがconnectsTo => 証明可能 (wfs-allRLHaveSameTypeCPRQ(S)がfalse)

   - Case 2-3-2-3: 対応するrelationshipがconnectsTo => 証明可能 (wfs-allRLHaveSameTypeCPRQ(S)がfalse)
   - ここでCase 2-3-2-3-2-3-1がまだ残っている。

### ステップ 2-4: 次状態に適用されるルールを考察
 - unboundなconnectsTo requirementがあるので、適用されるルールはR11。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R11の条件節は「unbound requiremetのnodeがcreated、かつ対応するopen messageが存在する」だが、まずnodeの条件で以下の3つにケース分けする。
 - Case 2-3-2-3-2-3-1-2-1: unbound requiremetのnodeがinitial => 証明可能 (Initial Cont Lemmaによりconst(S')がtrue)
 - Case 2-3-2-3-2-3-1-2-2: unbound requiremetのnodeがcreated => 証明可能 (Created Cont Lemmaによりconst(S')がtrue)
 - Case 2-3-2-3-2-3-1-2-3: unbound requiremetのnodeがstarted => 証明可能 (inv-ifNDStartedThenRQReady(S)がfalse)

## R11に対するCondtion (2)の証明譜 (Proof-contcont-R11.cafe)
### ステップ 2-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R11のLHSはunbound requirementに対応するrelationshipと、対応するopen messageが必要なので、< sND, sCP, (req(connectsTo,idRQ,unbound,idND') sRQ), (rel(connectsTo,idRL,idCP,idRQ) sRL), (opMsg(idCP) mp) >が最も一般的な状態。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - requirementの親nodeのリンクが未定なので、以下の２つにケース分けする
 - Case 1: 対応するnodeが無い => 証明可能 (wfs-allRQHaveND(S)がfalse)
 - Case 2: 対応するnodeがある

### ステップ 2-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R11の条件節は「unbound requiremetのnodeがcreated、かつcapabilityがisActivated」なので、まずはnodeの状態について以下の３つにケース分け。
 - Case 2-1: requirementに対応するnodeがinitial => 証明可能 (Initial Cont Lemmaによりcont(S')がtrue)
 - Case 2-2: requirementに対応するnodeがcreated => 証明可能 (Created Cont Lemmaによりcont(S')がtrue)
 - Case 2-3: requirementに対応するnodeがstarted => 証明可能 (次状態が無い)

## R12に対するCondtion (2)の証明譜 (Proof-contcont-R12.cafe)
### ステップ 2-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R12のLHSはwaiting requirementに対応するrelationshipと、さらにそれに対応するavailable capabilityが必要なので、< sND, (cap(dependsOn,idCP,available,idND) sCP), (req(dependsOn,idRQ,waiting,idND') sRQ), (rel(dependsOn,idRL,idCP,idRQ) sRL), mp >が最も一般的な状態。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - requirementの親nodeのリンクが未定なので、以下の２つにケース分けする
 - Case 1: 対応するnodeが無い => 証明可能 (wfs-allRQHaveND(S)がfalse)
 - Case 2: 対応するnodeがある

### ステップ 2-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R12は無条件ルール。

### ステップ 2-3: ルール適用後の次状態がfinalになる/ならないでケース分け
 - R12適用直後にfinalにならないことはわかっている。

### ステップ 2-4: 次状態に適用されるルールを考察
 - readyなrequirementがあるので、適用されるルールはR02。

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R02のLHSはrequiremntに対応するcreated nodeが必要なので、cspコマンドで以下の３つにケース分けする。
 - Case 2-1: requirementに対応するnodeがinitial => 証明可能 (inv-ifNDInitialThenRQUnboundReady(S)がfalse)
 - Case 2-2: requirementに対応するnodeがcreated => 証明可能 (R02が適用可能なのでcont(S')がtrue)
 - Case 2-3: requirementに対応するnodeがstarted => 証明可能 (inv-ifNDStartedThenRQReady(S)がfalse)

## Condtion (3): inv(S) and not final(S) implies m(S) > m(SS) の証明譜 (Proof-measure.cafe)
### ステップ 3-0: 証明すべき述語を定義
 - mmes = wfs and inv and not final implies m > m'
 - wfsを、invと区別して定義しているので前件に加えておく。
 - 次状態が存在する状態に関する条件なので、前件にcont(S)が不要であることに注意。
 - mesmesを二重否定イディオムを使って定義する。
 - 自然数に対するAxiomとして N < N+1, N < N+2, N < N+3, N < N+4, を定義しておく。

## R01に対するCondtion (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R01のLHSを任意定数tnd, idND, sND, sCP, sRQ, sRL, mpで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initial nodeのhostedOn requirementがすべてready」なので以下の２つにケース分けする。
 - Case 1: initial nodeのhostedOn requirementがすべてready => 証明可能 (m(S) > m(SS)が成り立つ)
 - Case 2: initial nodeのhostedOn requirementがすべてready、ではない => 証明可能 (次状態が無い)

## R02に対するCondtion (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R02のLHSを任意定数tnd, idND, sND, sCP, sRQ, sRL, mpで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R02の条件節は「created nodeのrequirementがすべてready」なので以下の２つにケース分けする。
 - Case 1: created nodeのrequirementがすべてready => 証明可能 (m(S) > m(SS)が成り立つ)
 - Case 2: created nodeのrequirementがすべてready、ではない => 証明可能 (次状態が無い)

## R03に対するCondtion (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R03のLHSを任意定数sND, idCP, idND, sCP, sRQ, sRL, mpで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R03の条件節は「closedなhostedOn capabilityに対するnodeがisCreated」なので以下の２つにケース分けする。
 - Case 1: closedなhostedOn capabilityに対するnodeがisCreated => 証明可能 (m(S) > m(SS)が成り立つ)
 - Case 2: closedなhostedOn capabilityに対するnodeがisCreated、ではない => 証明可能 (次状態が無い)

## R04に対するCondtion (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R04のLHSを任意定数sND, idCP, idND, sCP, idRQ, idND', sRQ, idRL, sRL, mpで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R04は無条件ルールなので、ケース分けは不要。
 - Case 1: R04のLHSにマッチする最も一般的なケース => 証明可能 (m(S) > m(SS)が成り立つ)

## R05に対するCondtion (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R05のLHSを任意定数sND, idCP, idND, sCP, sRQ, sRL, mpで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R05の条件節は「closedなdependsOn capabilityに対するnodeがisCreated」なので以下の２つにケース分けする。
 - Case 1: closedなdependsOn capabilityに対するnodeがisCreated => 証明可能 (m(S) > m(SS)が成り立つ)
 - Case 2: closedなdependsOn capabilityに対するnodeがisCreated、ではない => 証明可能 (次状態が無い)

## R06に対するCondtion (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R06のLHSを任意定数sND, idCP, idND, sCP, sRQ, sRL, mpで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R06の条件節は「openなdependsOn capabilityに対するnodeがstarted」なので以下の２つにケース分けする。
 - Case 1: openなdependsOn capabilityに対するnodeがstarted => 証明可能 (m(S) > m(SS)が成り立つ)
 - Case 2: openなdependsOn capabilityに対するnodeがstarted、ではない => 証明可能 (次状態が無い)

## R07に対するCondtion (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R07のLHSを任意定数sND, idCP, idND, sCP, idRQ, idND', sRQ, idRL, sRL, mpで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R07の条件節は「requiementに対するnodeがcreated、かつcapabilityがisActivated」なので以下の２つにケース分けする。
 - Case 1: requiementに対するnodeがcreated、かつcapabilityがisActivated => 証明可能 (m(S) > m(SS)が成り立つ)
 - Case 2: requiementに対するnodeがcreated、かつcapabilityがisActivated、ではない => 証明可能 (次状態が無い)

## R08に対するCondtion (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R08のLHSを任意定数sND, idCP, idND, sCP, idRQ, idND', sRQ, idRL, sRL, mpで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R08は無条件ルールなので、ケース分けは不要。
 - Case 1: R08のLHSにマッチする最も一般的なケース => 証明可能 (m(S) > m(SS)が成り立つ)

## R09に対するCondtion (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R09のLHSを任意定数sND, idCP, idND, sCP, sRQ, sRL, mpで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R05の条件節は「closedなconnectsTo capabilityに対するnodeがisCreated」なので以下の２つにケース分けする。
 - Case 1: closedなconnectsTo capabilityに対するnodeがisCreated => 証明可能 (m(S) > m(SS)が成り立つ)
 - Case 2: closedなconnectsTo capabilityに対するnodeがisCreated、ではない => 証明可能 (次状態が無い)

## R10に対するCondtion (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R10のLHSを任意定数sND, idCP, idND, sCP, sRQ, sRL, mpで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R10の条件節は「openなconnectsTo capabilityに対するnodeがstarted」なので以下の２つにケース分けする。
 - Case 1: openなconnectsTo capabilityに対するnodeがstarted => 証明可能 (m(S) > m(SS)が成り立つ)
 - Case 2: openなconnectsTo capabilityに対するnodeがstarted、ではない => 証明可能 (次状態が無い)

## R11に対するCondtion (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R11のLHSを任意定数sND, sCP, idRQ, idND, sRQ, idRL, idCP, sRL, mpで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R11の条件節は「requiementに対するnodeがcreated」なので以下の２つにケース分けする。
 - Case 1: requiementに対するnodeがcreated => 証明可能 (m(S) > m(SS)が成り立つ)
 - Case 2: requiementに対するnodeがcreated、ではない => 証明可能 (次状態が無い)

## R12に対するCondtion (3)の証明譜
### ステップ 3-1: 各ルールのLHSにマッチする最も一般的なケースから開始
 - R12のLHSを任意定数sND, sCP, idRQ, idND, sRQ, idRL, idCP, sRL, mpで表現する。

### ステップ 3-2: ルールの条件節が成り立つ/成り立たないでケース分け
 - R12は無条件ルールなので、ケース分けは不要。
 - Case 1: R12のLHSにマッチする最も一般的なケース => 証明可能 (m(S) > m(SS)が成り立つ)

## Condtion (4): inv(S) and (cont(S) or final(S)) and m(S) = 0 implies final(S) の証明譜 (Proof-measure.cafe)
### ステップ 4-0: 証明すべき述語を定義
 - mesfinal = wfs and inv and (cont or final) and m = 0 implies final .
 - wfsを、invと区別して定義しているので前件に加えておく。

### ステップ 4-1: m(S)用の一般Lemmaをインスタンシエート
 - initial nodeの数が0、かつcreated nodeの数が0ならば、すべてのnodeはstartedである。

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
 - 個々のinvariantの証明譜の説明は割愛する。

## Initial Cont Lemmaの証明譜(Proof-cyclelemma.cafe)
### ステップ 2-0: 証明すべき述語を定義
 - invcont = wfs and inv implies cont
 - Sにinitial nodeが含まれる時に、invcont(S)が成り立つことを証明する。

### ステップ 2-1: 最も一般的なケースから開始
 - 一つ以上のinitial nodeが存在する場合は、< (node(tnd, idND, initial) sND), sCP, sRQ, sRL, mp >が最も一般的な状態。
 - ここで、idND nodeは任意に選択しているので、Cyclic Dependency Lemmaが存在を保証する「initialであって、かつDDSR01にinitialなnodeが含まれないnode」であることを仮定してよい。

### ステップ 2-4: 次状態に適用されるルールを考察
 - initialなnodeがあるので、適用されるルールはR01。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R01の条件節は「initial nodeのhostedOn requirementがすべてready」なので以下の3つにケース分けする。
 - Case 1: initial nodeのhostedOn requirementがすべてready => 証明可能 (R01が適用可能なのでcont(S)がtrue)
 - Case 2: initial nodeのhostedOn requirementの一つがunbound.
 - Case 3: initial nodeのhostedOn requirementの一つがwaiting. =>  証明可能 (inv-HostedOnRQNotWaiting(S)がfalse)

### ステップ 2-4: 次状態に適用されるルールを考察
 - unboundなhostedOn requirementがあるので、適用されるルールはR04。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - requirementに対するrelationshipのリンクが未定なので、以下の２つにケース分けする
   - Case 2-1: 対応するrelationshipが無い => 証明可能 (wfs-allRQHaveRL(S)がfalse)
   - Case 2-2: 対応するrelationshipがある

 - relationshipに対するcapabilityのリンクが未定なので、以下の２つにケース分けする
   - Case 2-2-1: 対応するcapabilityが無い => 証明可能 (wfs-allRLHaveCP(S)がfalse)
   - Case 2-2-2: 対応するcapabilityがある
   
 - capabilityの親ノードのIDがすでに存在するものかどうかで、以下の２つにケース分けする
   - Case 2-2-2-1: capabilityの親ノードはrequirementの親ノードと同じ => 証明可能 (wfs-allRLNotInSameND(S)がfalse)
   - Case 2-2-2-2: capabilityの親ノードはrequirementの親ノードと異なる

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R04のLHSはrequiremntに対応するavailable capabilityが必要なので、cspコマンドで以下の３つにケース分けする。
 - Case 2-2-2-2-1: 対応するcapabilityがclosed
 - Case 2-2-2-2-2: 対応するcapabilityがopen => 証明可能 (inv-HostedOnCPNotOpen(S)がfalse)
 - Case 2-2-2-2-3: 対応するcapabilityがavailable => 証明可能 (R04が適用可能なのでcont(S)がtrue)

### ステップ 2-4: 次状態に適用されるルールを考察
 - closedなhostedOn capabilityがあるので、適用されるルールはR03。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親ノードのリンクが未定なので、以下の２つにケース分けする
   - Case 2-2-2-2-1-1: 対応するnodeが無い => 証明可能 (wfs-allCPHaveND(S)がfalse)
   - Case 2-2-2-2-1-2: 対応するnodeがある

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R03の条件節はcapabilityに対応するnodeがcreatedまたはstartedなので、以下の３つにケース分けする
   - Case 2-2-2-2-1-2-1: capabilityの親nodeがinitial => 証明可能 (元のnodeのDDSR01にinitial nodeが存在して矛盾)
   - Case 2-2-2-2-1-2-2: capabilityの親nodeがcreated => 証明可能 (R03が適用可能なのでcont(S)がtrue)
   - Case 2-2-2-2-1-2-3: capabilityの親nodeがstarted => 証明可能 (R03が適用可能なのでcont(S)がtrue)

## Created Cont Lemmaの証明譜(Proof-cyclelemma.cafe)
### ステップ 2-0: 証明すべき述語を定義
 - invcont = wfs and inv implies cont
 - Sにcreated nodeが含まれる時に、invcont(S)が成り立つことを証明する。
 - 上記で証明済みのInitial Cont Lemmaを導入しておく。 

### ステップ 2-1: 最も一般的なケースから開始
 - 一つ以上のcreated nodeが存在する場合は、< (node(tnd, idND, created) sND), sCP, sRQ, sRL, mp >が最も一般的な状態。
 - ここで、idND nodeは任意に選択しているので、Cyclic Dependency Lemmaが存在を保証する「createdであって、かつDDSR02にcreatedなnodeが含まれないnode」であることを仮定してよい。

### ステップ 2-4: 次状態に適用されるルールを考察
 - createdなnodeがあるので、適用されるルールはR02。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R02の条件節は「created nodeのrequirementがすべてready」なので以下の3つにケース分けする。
 - Case 1: created nodeのrequirementがすべてready => 証明可能 (R02が適用可能なのでcont(S)がtrue)
 - Case 2: created nodeのrequirementの一つがunbound.
 - Case 3: created nodeのrequirementの一つがwaiting.

### Case 2: created nodeのrequirementの一つがunboundの証明。
### ステップ 2-4: 次状態に適用されるルールを考察
 - unboundなrequirementのタイプによって適用されるルールが異なるので、以下の３つにケース分け
 - Case 2-1: unboundなrequirementがhostedOn => 証明可能 (inv-ifNDCreatedThenHostedOnRQReady(S)がfalse)
 - Case 2-2: unboundなrequirementがdependsOn
 - Case 2-3: unboundなrequirementがconnectsTo

### Case 2-2: unboundなrequirementがdependsOnの証明
### ステップ 2-4: 次状態に適用されるルールを考察
 - unboundなdependsOn requirementがあるので、適用されるルールはR07。

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R07のLHSはrequiremntに対応するrelationishipと、されにそれに対応するcapabilityが必要。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - requirementに対するrelationshipのリンクが未定なので、以下の２つにケース分けする
   - Case 2-2-1: 対応するrelationshipが無い => 証明可能 (wfs-allRQHaveRL(S)がfalse)
   - Case 2-2-2: 対応するrelationshipがある

 - relationshipに対するcapabilityのリンクが未定なので、以下の２つにケース分けする
   - Case 2-2-2-1: 対応するcapabilityが無い => 証明可能 (wfs-allRLHaveCP(S)がfalse)
   - Case 2-2-2-2: 対応するcapabilityがある
   
 - capabilityの親ノードのIDがすでに存在するものかどうかで、以下の２つにケース分けする
   - Case 2-2-2-2-1: capabilityの親ノードはrequirementの親ノードと同じ => 証明可能 (wfs-allRLNotInSameND(S)がfalse)
   - Case 2-2-2-2-2: capabilityの親ノードはrequirementの親ノードと異なる

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R07のLHSはrequiremntに対応するactivatedなcapabilityが必要なので、cspコマンドで以下の３つにケース分けする。
 - Case 2-2-2-2-2-1: 対応するcapabilityがclosed
 - Case 2-2-2-2-2-2: 対応するcapabilityがopen => 証明可能 (R07が適用可能なのでcont(S)がtrue)
 - Case 2-2-2-2-2-3: 対応するcapabilityがavailable => 証明可能 (R07が適用可能なのでcont(S)がtrue)

### ステップ 2-4: 次状態に適用されるルールを考察
 - closedなdepensOn capabilityがあるので、適用されるルールはR05。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R05の条件節はcapabilityの親nodeがcreatedかstartedであることを要求する

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親ノードのリンクが未定なので、以下の２つにケース分けする
   - Case 2-2-2-2-2-1-1: 対応するnodeが無い => 証明可能 (wfs-allCPHaveND(S)がfalse)
   - Case 2-2-2-2-2-1-2: 対応するnodeがある

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R05の条件節はcapabilityに対応するnodeがcreatedまたはstartedなので、以下の３つにケース分けする
   - Case 2-2-2-2-2-1-2-1: capabilityの親nodeがinitial => 証明可能 (Initial Cont Lemmaによりcont(S)がtrue)
   - Case 2-2-2-2-2-1-2-2: capabilityの親nodeがcreated => 証明可能 (R05が適用可能なのでcont(S)がtrue)
   - Case 2-2-2-2-2-1-2-3: capabilityの親nodeがstarted => 証明可能 (R05が適用可能なのでcont(S)がtrue)

### Case 2-3: unboundなrequirementがconnectsToの証明
### ステップ 2-4: 次状態に適用されるルールを考察
 - unboundなconnectsTo requirementがあるので、適用されるルールはR11。

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R11のLHSはrequiremntに対応するrelationishipが必要。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - requirementに対するrelationshipのリンクが未定なので、以下の２つにケース分けする
   - Case 2-3-1: 対応するrelationshipが無い => 証明可能 (wfs-allRQHaveRL(S)がfalse)
   - Case 2-3-2: 対応するrelationshipがある

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R11のLHSはrequiremntに対応するopen messageが必要なので、以下の2つにケース分けする。
 - Case 2-3-2-1: 対応するopen messageが無い
 - Case 2-3-2-2: 対応するopen messageがある => 証明可能 (R11が適用可能なのでcont(S)がtrue)

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - open messageに対するcapabilityのリンクが未定なので、以下の２つにケース分けする
   - Case 2-3-2-1-1: 対応するcapabilityが無い => 証明可能 (wfs-allRLHaveCP(S)がfalse)
   - Case 2-3-2-1-2: 対応するcapabilityがある
   
 - capabilityの親ノードのIDがすでに存在するものかどうかで、以下の２つにケース分けする
   - Case 2-3-2-1-2-1: capabilityの親ノードはrequirementの親ノードと同じ => 証明可能 (wfs-allRLNotInSameND(S)がfalse)
   - Case 2-3-2-1-2-2: capabilityの親ノードはrequirementの親ノードと異なる

### ステップ 2-4: 次状態に適用されるルールを考察
 - connectsTo capabilityの状態によって適用されるルールが異なるので、以下の３つにケース分け
 - Case 2-3-2-1-2-2-1: Capabilityがclosed
 - Case 2-3-2-1-2-2-2: Capabilityがopen
 - Case 2-3-2-1-2-2-3: Capabilityがavailable => 証明可能 (inv-ifConnectsToCPAvailableThenRQWaitingReadyOrOpenMsg(S)がfalse)

### Case 2-3-2-1-2-2-1: Capabilityがclosedの証明
### ステップ 2-4: 次状態に適用されるルールを考察
 - closedなconnectsTo capabilityがあるので、適用されるルールはR09。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R09の条件節はcapabilityの親nodeがcreatedまたはstartedであることを要求する

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親ノードのリンクが未定なので、以下の２つにケース分けする
   - Case 2-3-2-1-2-2-1-1: 対応するnodeが無い => 証明可能 (wfs-allCPHaveND(S)がfalse)
   - Case 2-3-2-1-2-2-1-2: 対応するnodeがある

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R09の条件節はcapabilityに対応するnodeがcreatedまたはstartedなので、以下の３つにケース分けする
   - Case 2-3-2-1-2-2-1-2-1: capabilityの親nodeがinitial => 証明可能 (Initial Cont Lemmaによりcont(S)がtrue)
   - Case 2-3-2-1-2-2-1-2-2: capabilityの親nodeがcreated => 証明可能 (R09が適用可能なのでcont(S)がtrue)
   - Case 2-3-2-1-2-2-1-2-3: capabilityの親nodeがstarted => 証明可能 (R09が適用可能なのでcont(S)がtrue)

### Case 2-3-2-1-2-2-2: Capabilityがopenの証明
### ステップ 2-4: 次状態に適用されるルールを考察
 - openなconnectsTo capabilityがあるので、適用されるルールはR10。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R10の条件節はcapabilityの親nodeがstartedであることを要求する

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親ノードのリンクが未定なので、以下の２つにケース分けする
   - Case 2-3-2-1-2-2-2-1: 対応するnodeが無い => 証明可能 (wfs-allCPHaveND(S)がfalse)
   - Case 2-3-2-1-2-2-2-2: 対応するnodeがある

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R09の条件節はcapabilityに対応するnodeがcreatedまたはstartedなので、以下の３つにケース分けする
   - Case 2-3-2-1-2-2-2-2-1: capabilityの親nodeがinitial => 証明可能 (Initial Cont Lemmaによりcont(S)がtrue)
   - Case 2-3-2-1-2-2-2-2-2: capabilityの親nodeがcreated => 証明可能 (inv-ifConnectsToCPOpenThenRQWaitingOrOpenMsg(S)がfalse)
   - Case 2-3-2-1-2-2-2-2-3: capabilityの親nodeがstarted => 証明可能 (R10が適用可能なのでcont(S)がtrue)

### Case 3: created nodeのrequirementの一つがwaitingの証明。
### ステップ 2-4: 次状態に適用されるルールを考察
 - waitingなrequirementのタイプによって適用されるルールが異なるので、以下の３つにケース分け
 - Case 3-1: waitingなrequirementがhostedOn => 証明可能 (inv-HostedOnRQNotWaiting(S)がfalse)
 - Case 3-2: waitingなrequirementがdependsOn
 - Case 3-3: waitingなrequirementがconnectsTo

### Case 3-2: waitingなrequirementがdependsOnの証明
### ステップ 2-4: 次状態に適用されるルールを考察
 - waitingなdependsOn requirementがあるので、適用されるルールはR08。

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R08のLHSはrequiremntに対応するrelationishipと、されにそれに対応するcapabilityが必要。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - requirementに対するrelationshipのリンクが未定なので、以下の２つにケース分けする
   - Case 3-2-1: 対応するrelationshipが無い => 証明可能 (wfs-allRQHaveRL(S)がfalse)
   - Case 3-2-2: 対応するrelationshipがある

 - relationshipに対するcapabilityのリンクが未定なので、以下の２つにケース分けする
   - Case 3-2-2-1: 対応するcapabilityが無い => 証明可能 (wfs-allRLHaveCP(S)がfalse)
   - Case 3-2-2-2: 対応するcapabilityがある
   
 - capabilityの親ノードのIDがすでに存在するものかどうかで、以下の２つにケース分けする
   - Case 3-2-2-2-1: capabilityの親ノードはrequirementの親ノードと同じ => 証明可能 (wfs-allRLNotInSameND(S)がfalse)
   - Case 3-2-2-2-2: capabilityの親ノードはrequirementの親ノードと異なる

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R08のLHSはrequiremntに対応するavailableなcapabilityが必要なので、cspコマンドで以下の３つにケース分けする。
 - Case 3-2-2-2-2-1: 対応するcapabilityがclosed => 証明可能 (inv-ifCPClosedThenRQUnbound(S)がfalse)
 - Case 3-2-2-2-2-2: 対応するcapabilityがopen
 - Case 3-2-2-2-2-3: 対応するcapabilityがavailable => 証明可能 (R08が適用可能なのでcont(S)がtrue)

### ステップ 2-4: 次状態に適用されるルールを考察
 - openなdepensOn capabilityがあるので、適用されるルールはR06。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R06の条件節はcapabilityの親nodeがstartedであることを要求する

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親ノードのリンクが未定なので、以下の２つにケース分けする
   - Case 3-2-2-2-2-1-1: 対応するnodeが無い => 証明可能 (wfs-allCPHaveND(S)がfalse)
   - Case 3-2-2-2-2-1-2: 対応するnodeがある

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R05の条件節はcapabilityに対応するnodeがcreatedまたはstartedなので、以下の３つにケース分けする
   - Case 3-2-2-2-2-1-2-1: capabilityの親nodeがinitial => 証明可能 (Initial Cont Lemmaによりcont(S)がtrue)
   - Case 3-2-2-2-2-1-2-2: capabilityの親nodeがcreated => 証明可能 (元のnodeのDDSR02にcreated nodeが存在して矛盾)
   - Case 3-2-2-2-2-1-2-3: capabilityの親nodeがstarted => 証明可能 (R06が適用可能なのでcont(S)がtrue)

### Case 3-3: waitingなrequirementがconnectsToの証明
### ステップ 2-4: 次状態に適用されるルールを考察
 - waitingなconnectsTo requirementがあるので、適用されるルールはR12。

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R12のLHSはrequiremntに対応するrelationishipが必要。

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - requirementに対するrelationshipのリンクが未定なので、以下の２つにケース分けする
   - Case 3-3-1: 対応するrelationshipが無い => 証明可能 (wfs-allRQHaveRL(S)がfalse)
   - Case 3-3-2: 対応するrelationshipがある

### ステップ 1-3: 最初のルールのLHSにマッチするケースを含むようにケース分け
 - R11のLHSはrequiremntに対応するavailable messageが必要なので、以下の2つにケース分けする。
 - Case 3-3-2-1: 対応するavailable messageが無い
 - Case 3-3-2-2: 対応するavailable messageがある => 証明可能 (R12が適用可能なのでcont(S)がtrue)

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - available messageに対するcapabilityのリンクが未定なので、以下の２つにケース分けする
   - Case 3-3-2-1-1: 対応するcapabilityが無い => 証明可能 (wfs-allRLHaveCP(S)がfalse)
   - Case 3-3-2-1-2: 対応するcapabilityがある
   
 - capabilityの親ノードのIDがすでに存在するものかどうかで、以下の２つにケース分けする
   - Case 3-3-2-1-2-1: capabilityの親ノードはrequirementの親ノードと同じ => 証明可能 (wfs-allRLNotInSameND(S)がfalse)
   - Case 3-3-2-1-2-2: capabilityの親ノードはrequirementの親ノードと異なる

### ステップ 2-4: 次状態に適用されるルールを考察
 - connectsTo capabilityの状態によって適用されるルールが異なるので、以下の３つにケース分け
 - Case 3-3-2-1-2-2-1: Capabilityがclosed => 証明可能 (inv-ifCPClosedThenRQUnbound(S)がfalse)
 - Case 3-3-2-1-2-2-2: Capabilityがopen
 - Case 3-3-2-1-2-2-3: Capabilityがavailable => 証明可能 (inv-ifConnectsToCPAvailableThenRQReadyOrAvailableMsg(S)がfalse)
 
### ステップ 2-4: 次状態に適用されるルールを考察
 - openなconnectsTo capabilityがあるので、適用されるルールはR10。

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R10の条件節はcapabilityの親nodeがstartedであることを要求する

### ステップ 1-5: 参照先が未定のリンクがあったら、参照先が無い/あるでケース分け
 - capabilityの親ノードのリンクが未定なので、以下の２つにケース分けする
   - Case 3-3-2-1-2-2-2-1: 対応するnodeが無い => 証明可能 (wfs-allCPHaveND(S)がfalse)
   - Case 3-3-2-1-2-2-2-2: 対応するnodeがある

### ステップ 1-4: 最初のルールの条件節が成り立つ/成り立たないでケース分け
 - R09の条件節はcapabilityに対応するnodeがcreatedまたはstartedなので、以下の３つにケース分けする
   - Case 3-3-2-1-2-2-2-2-1: capabilityの親nodeがinitial => 証明可能 (Initial Cont Lemmaによりcont(S)がtrue)
   - Case 3-3-2-1-2-2-2-2-2: capabilityの親nodeがcreated => 証明可能 (元のnodeのDDSR02にcreated nodeが存在して矛盾)
   - Case 3-3-2-1-2-2-2-2-3: capabilityの親nodeがstarted => 証明可能 (R10が適用可能なのでcont(S)がtrue)

## その他のLemmaの証明譜(Proof-lemma.cafe)

以上で、すべての十分条件が証明済みとなり、init leads-to finalが証明できた。

