import Init

namespace G449FiniteCoverage

/-- The ith original label in base 3; labels 0,1,2 stand for colours 2,3,4. -/
def label (w i : Nat) : Nat := (w / 3^i) % 3

def perms : List (List Nat) := [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]
def rule : List (List Nat) := [[0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 3, 3, 3], [0, 0, 1, 0, 3, 3, 4], [0, 0, 1, 4, 0, 4, 4], [0, 0, 1, 4, 4, 0, 4], [0, 1, 0, 4, 0, 4, 4]]
def exclusions : List (List Nat) := [[], [1080, 2133], [738, 1467, 1062, 2115], [1008, 1737, 1035, 2007], [846, 1575, 1683], [1002, 1245, 1029, 2001]]

def perm (p a : Nat) : Nat := (perms.getD p []).getD a 0

def transform (w r p : Nat) : Nat :=
  ((List.range 7).map fun i => perm p (label w ((i+r)%7)) * 3^i).sum

def isMatch (c w : Nat) : Bool :=
  (List.range 7).all fun i =>
    let req := (rule.getD c []).getD i 3
    if req == 3 then true else if req == 4 then label w i != 0 else label w i == req

def allowed (c w : Nat) : Bool :=
  isMatch c w && !(exclusions.getD c []).contains w

def witnessOK (w h : Nat) : Bool :=
  let c := h / 42
  let r := (h % 42) / 6
  let p := h % 6
  decide (c < 6) && decide (r < 7) && decide (p < 6) && allowed c (transform w r p)

def checkBlock (offset count packed : Nat) : Bool :=
  (List.range count).all fun i => witnessOK (offset+i) ((packed / 256^i)%256)

theorem witnessOK_sound (w h : Nat) (chk : witnessOK w h = true) :
    ∃ c r p, c < 6 ∧ r < 7 ∧ p < 6 ∧ allowed c (transform w r p) = true := by
  unfold witnessOK at chk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at chk
  exact ⟨h/42,(h%42)/6,h%6,chk.1.1.1,chk.1.1.2,chk.1.2,chk.2⟩

theorem checkBlock_sound (offset count packed i : Nat)
    (h : checkBlock offset count packed = true) (hi : i < count) :
    ∃ c r p, c < 6 ∧ r < 7 ∧ p < 6 ∧ allowed c (transform (offset+i) r p) = true :=
  witnessOK_sound _ _ (List.all_eq_true.mp h i (List.mem_range.mpr hi))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block0 : checkBlock 0 81 233598495570378250806783643252103266317043024665110484961095125696082891884689423208223036298164304649197354963974886013696493382187460288727771764464216243167248512783237548076571626149798691328 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block81 : checkBlock 81 81 242759053030167232815945795671155789985409467898777639678064524327303520474462003668141427660967383614854944173880577780659161576245302878491562131259883017077863655835803743970314736261789659184 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block162 : checkBlock 162 81 261078954871933618163951021067582124118472243598947746605122890892219595124772540590357266764293601947885972831685442496231814325821525561490955473760117765971399608924142203430827036101785497905 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block243 : checkBlock 243 81 233596995647858923054374553778219288047013183467805189046268214508877835590391485037126254802046452597554092696229336095959521921638995776526787294048390897974437385193648262347435861844455470646 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block324 : checkBlock 324 81 242757660662874919142739046405892885326750344220221083917530207733521448865633126433015840696928936810238713944995140805693191315939254158061016996533216091889943801598067875279271032931061084208 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block405 : checkBlock 405 81 270239619955159359151471213478216033880229559626602612571167185124416386587509538681211024448099860566702502623377079203193689847765370298467563830410981305872846618630650757102121026759179710769 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block486 : checkBlock 486 81 233596972726692911797339879433038568552809408707816690331897796542697836701031977807699671446056368487100970527187368243311799044063915257392658530443438112166013215294755156434361567457106671415 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block567 : checkBlock 567 81 242757637809918652784860036367066500108387576911340341022606216704804121983957171068822061728547663367010132036149006879701671261186743646252307508119872618173585017223826360533380755602780729392 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block648 : checkBlock 648 81 288560950121610841122528688849934601365933420106230589710430101707348105028203811882986116820353772629534381810545099173197617167241093402996681871159030605454373988929234650935292674876051108145 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block729 : checkBlock 729 81 233596995551855725541323082300030803202937292359344947452184108676561787350409160770537692359132108302183121355201849815484140499372852800746269012321283117147616449897964187383700607803168930876 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block810 : checkBlock 810 81 242757660633479756953437828330606675870991312527440336347460003587470608635716280878514709837150062314789416136438640385304797706038512180516433465654600099951034480220806327566361247159409455152 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block891 : checkBlock 891 81 261078954898490517799347863573957607289035780721580440041530564187450529398090143868052630614211236419212916633983148109602137830906526914301264726462120285409494912296960310767255439685014597937 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block972 : checkBlock 972 81 234042528717181183418324318919540214873399056464146558363393318788238479341814662370213454943685547553117900029771203508492874283042350641921063891505697238796296010087116027006901342685044815414 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block1053 : checkBlock 1053 81 243167536133615242965309048011529823250426753877666207767137947902719737054766081399598184373803029760935305524208903777207684896582755196967546859250123329573909096197044272183164005657789614640 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block1134 : checkBlock 1134 81 270239619979591706816095457981759578908784474019695333623161944704803161776518373572913237685652151752578678485008674832484645131651690098478559029123881268020120101939472027154539582566297586225 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block1215 : checkBlock 1215 81 233596972708634220046516040265520018107293407210722871690130324761727737381686532618230181717396107631765252270924134743976515150288019997876572924566815098061727039333304724640095826035005142839 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block1296 : checkBlock 1296 81 242757637789735409063263815792652214044777379651658367283904382426407040679804384940028999834833220415337731321599810251101404747271349130633536888266940289181974135849950419941145463062289985584 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block1377 : checkBlock 1377 81 297721615204836582110545472622948069742574879495263927026997162769891635130464329234100832540552439547533114636892861443583755589126022310903589992121001312724944703288787649121706348622845653297 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block1458 : checkBlock 1458 81 233596979841859350410236029678116969905391098252019951887388656642576103048991700533012775827435290054215531051222480997453050205499472002423221448333155512725988715866091196952500641722609253693 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block1539 : checkBlock 1539 81 242757644367522951035104395217814082270430064892579206916603676988343288424205353739838774198421831555303592061601225470016473765864327239470614193833601089627239745637165890443856529614449946672 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block1620 : checkBlock 1620 81 261078954871933618158503638885372329481358874102753022400063576645019462994890682352342773927338263307338578402935685530290176730819648808304584165858843488228582000056417429135045709636264079665 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block1701 : checkBlock 1701 81 233596979874922690467531704444208468473904390576678768852535298114926549976162920513313075970421545086701116839225641773110087357313973646760235918303204464421002190529740845500647873152676148790 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block1782 : checkBlock 1782 81 242757644348401981324455597774025398291802476599899866017262006513923444307265679272089786603343314950762355599868709036497696786557410454742137226384419914091578206129246181604878931858088276016 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block1863 : checkBlock 1863 81 270239619955159359146518490389624289228827985406667067735940754492249427771097643856868026330660598292603158769702621539148640394889884843727354214771811844616843597525817885356470148764540154161 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block1944 : checkBlock 1944 81 233596966743954171697131122173269536827873131523244648158156932471750365715239723294892092910038673269762753443305390282983214875520104512825451925466271100567674184985331367606275236953293535031 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block2025 : checkBlock 2025 81 242757631283294575622686075159101485622737959061201297478146542421980197732611064420882925338069862989886592270145144867963212488067375521942218559772600622512613023533345796176649549356009730096 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block2106 : checkBlock 2106 81 14957510853214220986070297605460668500253164790317985866881223418355287504153622958232825285223050443634465396304455464619052002242025373047803482439077980543175970753349341894096840430535258417 = true := by decide +kernel

/-- Every raw seven-neighbour assignment, modulo rotation and relabelling
the three noncentral colours, satisfies an allowed branch pattern. -/
theorem orbit_case_coverage (w : Nat) (hw : w < 2187) :
    ∃ c r p, c < 6 ∧ r < 7 ∧ p < 6 ∧ allowed c (transform w r p) = true := by
  by_cases h0 : w < 81
  · have m := checkBlock_sound 0 81 _ (w-0) block0 (by omega)
    rwa [show 0+(w-0)=w by omega] at m
  by_cases h81 : w < 162
  · have m := checkBlock_sound 81 81 _ (w-81) block81 (by omega)
    rwa [show 81+(w-81)=w by omega] at m
  by_cases h162 : w < 243
  · have m := checkBlock_sound 162 81 _ (w-162) block162 (by omega)
    rwa [show 162+(w-162)=w by omega] at m
  by_cases h243 : w < 324
  · have m := checkBlock_sound 243 81 _ (w-243) block243 (by omega)
    rwa [show 243+(w-243)=w by omega] at m
  by_cases h324 : w < 405
  · have m := checkBlock_sound 324 81 _ (w-324) block324 (by omega)
    rwa [show 324+(w-324)=w by omega] at m
  by_cases h405 : w < 486
  · have m := checkBlock_sound 405 81 _ (w-405) block405 (by omega)
    rwa [show 405+(w-405)=w by omega] at m
  by_cases h486 : w < 567
  · have m := checkBlock_sound 486 81 _ (w-486) block486 (by omega)
    rwa [show 486+(w-486)=w by omega] at m
  by_cases h567 : w < 648
  · have m := checkBlock_sound 567 81 _ (w-567) block567 (by omega)
    rwa [show 567+(w-567)=w by omega] at m
  by_cases h648 : w < 729
  · have m := checkBlock_sound 648 81 _ (w-648) block648 (by omega)
    rwa [show 648+(w-648)=w by omega] at m
  by_cases h729 : w < 810
  · have m := checkBlock_sound 729 81 _ (w-729) block729 (by omega)
    rwa [show 729+(w-729)=w by omega] at m
  by_cases h810 : w < 891
  · have m := checkBlock_sound 810 81 _ (w-810) block810 (by omega)
    rwa [show 810+(w-810)=w by omega] at m
  by_cases h891 : w < 972
  · have m := checkBlock_sound 891 81 _ (w-891) block891 (by omega)
    rwa [show 891+(w-891)=w by omega] at m
  by_cases h972 : w < 1053
  · have m := checkBlock_sound 972 81 _ (w-972) block972 (by omega)
    rwa [show 972+(w-972)=w by omega] at m
  by_cases h1053 : w < 1134
  · have m := checkBlock_sound 1053 81 _ (w-1053) block1053 (by omega)
    rwa [show 1053+(w-1053)=w by omega] at m
  by_cases h1134 : w < 1215
  · have m := checkBlock_sound 1134 81 _ (w-1134) block1134 (by omega)
    rwa [show 1134+(w-1134)=w by omega] at m
  by_cases h1215 : w < 1296
  · have m := checkBlock_sound 1215 81 _ (w-1215) block1215 (by omega)
    rwa [show 1215+(w-1215)=w by omega] at m
  by_cases h1296 : w < 1377
  · have m := checkBlock_sound 1296 81 _ (w-1296) block1296 (by omega)
    rwa [show 1296+(w-1296)=w by omega] at m
  by_cases h1377 : w < 1458
  · have m := checkBlock_sound 1377 81 _ (w-1377) block1377 (by omega)
    rwa [show 1377+(w-1377)=w by omega] at m
  by_cases h1458 : w < 1539
  · have m := checkBlock_sound 1458 81 _ (w-1458) block1458 (by omega)
    rwa [show 1458+(w-1458)=w by omega] at m
  by_cases h1539 : w < 1620
  · have m := checkBlock_sound 1539 81 _ (w-1539) block1539 (by omega)
    rwa [show 1539+(w-1539)=w by omega] at m
  by_cases h1620 : w < 1701
  · have m := checkBlock_sound 1620 81 _ (w-1620) block1620 (by omega)
    rwa [show 1620+(w-1620)=w by omega] at m
  by_cases h1701 : w < 1782
  · have m := checkBlock_sound 1701 81 _ (w-1701) block1701 (by omega)
    rwa [show 1701+(w-1701)=w by omega] at m
  by_cases h1782 : w < 1863
  · have m := checkBlock_sound 1782 81 _ (w-1782) block1782 (by omega)
    rwa [show 1782+(w-1782)=w by omega] at m
  by_cases h1863 : w < 1944
  · have m := checkBlock_sound 1863 81 _ (w-1863) block1863 (by omega)
    rwa [show 1863+(w-1863)=w by omega] at m
  by_cases h1944 : w < 2025
  · have m := checkBlock_sound 1944 81 _ (w-1944) block1944 (by omega)
    rwa [show 1944+(w-1944)=w by omega] at m
  by_cases h2025 : w < 2106
  · have m := checkBlock_sound 2025 81 _ (w-2025) block2025 (by omega)
    rwa [show 2025+(w-2025)=w by omega] at m
  by_cases h2106 : w < 2187
  · have m := checkBlock_sound 2106 81 _ (w-2106) block2106 (by omega)
    rwa [show 2106+(w-2106)=w by omega] at m
  omega


set_option maxRecDepth 32768 in
set_option maxHeartbeats 20000000 in
theorem accepted_patterns_count :
    ((List.range 2187).filter fun w => (List.range 6).any fun c => allowed c w).length = 53 := by decide +kernel

#print axioms orbit_case_coverage
#print axioms accepted_patterns_count
end G449FiniteCoverage
