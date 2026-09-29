-- Prove2me | Definitions.Def_mme_dwz_fourth_tensor_ledger_metadata_data
-- name    : mme_dwz_fourth_tensor_ledger_metadata_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T05:02:46.488298+00:00
-- url     : https://prove2.me/theorems/7b2ed4ce-a652-46c3-a60a-d97b4ee8767e
-- title:
--   Tensor metadata for the 180 proper fourth-power ledger rows
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_tensor_ledger_metadata, from the exact fourth-power scalar assembly.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Definitions.Def_mme_dwz_fourth_scalar_ledger_induction_facade_data
import Theorems.Thm_mme_dwz_fourth_scalar_ledger_induction_facade

open MME
open MME.DWZFourthScalarLedgerInduction
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthTensorLedger

/-- An exact canonical block address.  The three constructors are the
grade-3 CW tensor, grade-5 CW square, and grade-9 CW fourth power. -/
inductive ComponentAddress where
  | base (i j k : Fin 3)
  | square (i j k : Fin 5)
  | fourth (i j k : Fin 9)
deriving DecidableEq, Repr

/-- Scalar extraction method selected for the source profile. -/
inductive ComponentMethod where
  | atomic
  | leGallBoundary
  | leGallInteriorUnique
  | sixRegion
deriving DecidableEq, Repr

/-- Source identity plus the literal canonical tensor-block address.
`sourceIndex` is zero-based within its MAT component layer;
`rotationLocalIds` keeps the source's one-based cyclic-profile ids. -/
structure ComponentMetadata where
  objectId : Nat
  sourceIndex : Nat
  address : ComponentAddress
  method : ComponentMethod
  rotationLocalIds : Fin 3 → Nat
  zDenominator : Nat
  zCounts : List Nat
deriving DecidableEq, Repr

/-- Generator-emitted DFS order.  Entry `i` describes scalar-ledger
node `i`; the global node is deliberately not included here. -/
def componentMetadata : Array ComponentMetadata := #[
  { objectId := 1, sourceIndex := 0, address := .base 0 0 2, method := .atomic, rotationLocalIds := ![1, 3, 6], zDenominator := 1, zCounts := [0, 0] },
  { objectId := 3, sourceIndex := 2, address := .base 0 2 0, method := .atomic, rotationLocalIds := ![3, 6, 1], zDenominator := 1, zCounts := [0, 0] },
  { objectId := 6, sourceIndex := 5, address := .base 2 0 0, method := .atomic, rotationLocalIds := ![6, 1, 3], zDenominator := 1, zCounts := [0, 0] },
  { objectId := 7, sourceIndex := 0, address := .square 0 0 4, method := .leGallBoundary, rotationLocalIds := ![1, 5, 15], zDenominator := 1, zCounts := [0, 0, 1] },
  { objectId := 11, sourceIndex := 4, address := .square 0 4 0, method := .leGallBoundary, rotationLocalIds := ![5, 15, 1], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 21, sourceIndex := 14, address := .square 4 0 0, method := .leGallBoundary, rotationLocalIds := ![15, 1, 5], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 139, sourceIndex := 0, address := .fourth 0 0 8, method := .leGallBoundary, rotationLocalIds := ![1, 9, 45], zDenominator := 1, zCounts := [0, 0, 0, 0, 1] },
  { objectId := 2, sourceIndex := 1, address := .base 0 1 1, method := .atomic, rotationLocalIds := ![2, 5, 4], zDenominator := 1, zCounts := [0, 0] },
  { objectId := 4, sourceIndex := 3, address := .base 1 0 1, method := .atomic, rotationLocalIds := ![4, 2, 5], zDenominator := 1, zCounts := [0, 0] },
  { objectId := 5, sourceIndex := 4, address := .base 1 1 0, method := .atomic, rotationLocalIds := ![5, 4, 2], zDenominator := 1, zCounts := [0, 0] },
  { objectId := 8, sourceIndex := 1, address := .square 0 1 3, method := .leGallBoundary, rotationLocalIds := ![2, 9, 13], zDenominator := 500000000000000, zCounts := [0, 249999999930157, 250000000069843] },
  { objectId := 15, sourceIndex := 8, address := .square 1 3 0, method := .leGallBoundary, rotationLocalIds := ![9, 13, 2], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 19, sourceIndex := 12, address := .square 3 0 1, method := .leGallBoundary, rotationLocalIds := ![13, 2, 9], zDenominator := 1000000000000000, zCounts := [499999999026019, 500000000973981, 0] },
  { objectId := 140, sourceIndex := 1, address := .fourth 0 1 7, method := .leGallBoundary, rotationLocalIds := ![2, 17, 43], zDenominator := 500000000000000, zCounts := [0, 0, 0, 249999999930157, 250000000069843] },
  { objectId := 9, sourceIndex := 2, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![3, 12, 10], zDenominator := 1000000000000000, zCounts := [37033909639967, 925932180476533, 37033909883500] },
  { objectId := 16, sourceIndex := 9, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![10, 3, 12], zDenominator := 1000000000000001, zCounts := [37034147523554, 925931705102510, 37034147373937] },
  { objectId := 18, sourceIndex := 11, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![12, 10, 3], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 141, sourceIndex := 2, address := .fourth 0 2 6, method := .leGallBoundary, rotationLocalIds := ![3, 24, 40], zDenominator := 500000000000000, zCounts := [0, 0, 104396358615782, 291207282763767, 104396358620451] },
  { objectId := 10, sourceIndex := 3, address := .square 0 3 1, method := .leGallBoundary, rotationLocalIds := ![4, 14, 6], zDenominator := 500000000000000, zCounts := [249999999930157, 250000000069843, 0] },
  { objectId := 12, sourceIndex := 5, address := .square 1 0 3, method := .leGallBoundary, rotationLocalIds := ![6, 4, 14], zDenominator := 1000000000000000, zCounts := [0, 499999999026019, 500000000973981] },
  { objectId := 20, sourceIndex := 13, address := .square 3 1 0, method := .leGallBoundary, rotationLocalIds := ![14, 6, 4], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 142, sourceIndex := 3, address := .fourth 0 3 5, method := .leGallBoundary, rotationLocalIds := ![4, 30, 36], zDenominator := 999999999999999, zCounts := [0, 27000872178013, 472997558144936, 473000711402473, 27000858274577] },
  { objectId := 143, sourceIndex := 4, address := .fourth 0 4 4, method := .leGallBoundary, rotationLocalIds := ![5, 35, 31], zDenominator := 1000000000000000, zCounts := [2425574292965, 130946259813371, 733256293279512, 130946298396153, 2425574217999] },
  { objectId := 144, sourceIndex := 5, address := .fourth 0 5 3, method := .leGallBoundary, rotationLocalIds := ![6, 39, 25], zDenominator := 500000000000000, zCounts := [10956781471144, 239043339596893, 239043087942206, 10956790989757, 0] },
  { objectId := 145, sourceIndex := 6, address := .fourth 0 6 2, method := .leGallBoundary, rotationLocalIds := ![7, 42, 18], zDenominator := 1000000000000000, zCounts := [169255248043705, 661488073559282, 169256678397013, 0, 0] },
  { objectId := 146, sourceIndex := 7, address := .fourth 0 7 1, method := .leGallBoundary, rotationLocalIds := ![8, 44, 10], zDenominator := 500000000000000, zCounts := [249999999930157, 250000000069843, 0, 0, 0] },
  { objectId := 147, sourceIndex := 8, address := .fourth 0 8 0, method := .leGallBoundary, rotationLocalIds := ![9, 45, 1], zDenominator := 1, zCounts := [1, 0, 0, 0, 0] },
  { objectId := 148, sourceIndex := 9, address := .fourth 1 0 7, method := .leGallBoundary, rotationLocalIds := ![10, 8, 44], zDenominator := 1000000000000000, zCounts := [0, 0, 0, 499999999026019, 500000000973981] },
  { objectId := 76, sourceIndex := 69, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![70, 71, 72], zDenominator := 1785714285714287500000000000000000000000000, zCounts := [492642438079960723539478769214872922017279, 800429409686470701693252242107980642034541, 492642437947856074767268988677146435948180] },
  { objectId := 77, sourceIndex := 70, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![71, 72, 70], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 78, sourceIndex := 71, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![72, 70, 71], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 149, sourceIndex := 10, address := .fourth 1 1 6, method := .sixRegion, rotationLocalIds := ![11, 16, 41], zDenominator := 1000000000000000000000000000000, zCounts := [0, 0, 15632850634043171218716057, 999968734317748997496639110491, 15632831616959332142173452] },
  { objectId := 22, sourceIndex := 15, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![16, 17, 18], zDenominator := 1000000000000001, zCounts := [403380669960589, 193238676801698, 403380653237714] },
  { objectId := 79, sourceIndex := 72, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![73, 74, 75], zDenominator := 250000000000000250000000000000000000000000000, zCounts := [45941122960708012251076140144517777679218, 249908124850363951706328992442183928707307189, 45934026675590281419931417671553515013593] },
  { objectId := 80, sourceIndex := 73, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![74, 75, 73], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 24, sourceIndex := 17, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![18, 16, 17], zDenominator := 250000000000000, zCounts := [9300034303238, 231399931410383, 9300034286379] },
  { objectId := 81, sourceIndex := 74, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![75, 73, 74], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 23, sourceIndex := 16, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![17, 18, 16], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 150, sourceIndex := 11, address := .fourth 1 2 5, method := .sixRegion, rotationLocalIds := ![12, 23, 37], zDenominator := 1000000000000001000000000000000, zCounts := [0, 1391521776134589574137594393, 498608940440923927790391158037, 498607997716856279216764679186, 1391540066086203418706568384] },
  { objectId := 25, sourceIndex := 18, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![19, 20, 21], zDenominator := 1000000000000001, zCounts := [48173663469861, 903652672867995, 48173663662145] },
  { objectId := 82, sourceIndex := 75, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![76, 77, 78], zDenominator := 500000000000000500000000000000, zCounts := [443788868851521641309261343, 499112421994817952773285917439, 443789136331025585404821218] },
  { objectId := 83, sourceIndex := 76, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![77, 78, 76], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 27, sourceIndex := 20, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![21, 19, 20], zDenominator := 1000000000000000, zCounts := [38923052937811, 922153894160729, 38923052901460] },
  { objectId := 84, sourceIndex := 77, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![78, 76, 77], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 26, sourceIndex := 19, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![20, 21, 19], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 151, sourceIndex := 12, address := .fourth 1 3 4, method := .sixRegion, rotationLocalIds := ![13, 29, 32], zDenominator := 1000000000000000000000000000000, zCounts := [15464618093589756823253913, 72089434438510093271636731687, 855790219898924325342553259309, 72089416398130957534313182364, 15464646341034094673572727] },
  { objectId := 28, sourceIndex := 21, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![22, 23, 24], zDenominator := 1000000000000000, zCounts := [39313745523889, 921372508914297, 39313745561814] },
  { objectId := 85, sourceIndex := 78, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![79, 80, 81], zDenominator := 500000000000000500000000000000000000000000000, zCounts := [417960473447237233797564891593552769052495, 499164079289789467080007871654752332621903977, 417960236763795686194563453654114609043528] },
  { objectId := 86, sourceIndex := 79, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![80, 81, 79], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 30, sourceIndex := 23, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![24, 22, 23], zDenominator := 999999999999999, zCounts := [48188160693555, 903623678219867, 48188161086577] },
  { objectId := 87, sourceIndex := 80, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![81, 79, 80], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 29, sourceIndex := 22, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![23, 24, 22], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 152, sourceIndex := 13, address := .fourth 1 4 3, method := .sixRegion, rotationLocalIds := ![14, 34, 26], zDenominator := 500000000000000000000000000000, zCounts := [6545319721929771451143411251, 243455685972824921709283755460, 243453601406799084028111867323, 6545392898446222811460965966, 0] },
  { objectId := 31, sourceIndex := 24, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![25, 26, 27], zDenominator := 1000000000000000, zCounts := [37627285994512, 924745428003365, 37627286002123] },
  { objectId := 88, sourceIndex := 81, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![82, 83, 84], zDenominator := 999999999999999000000000000000000000000000000, zCounts := [41033538733643872391270594034920771161044, 999917933122326811963530888406863586780164109, 41033338938544164077840999101492448674847] },
  { objectId := 89, sourceIndex := 82, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![83, 84, 82], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 33, sourceIndex := 26, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![27, 25, 26], zDenominator := 1000000000000000, zCounts := [404661808449122, 190676382719271, 404661808831607] },
  { objectId := 90, sourceIndex := 83, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![84, 82, 83], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 32, sourceIndex := 25, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![26, 27, 25], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 153, sourceIndex := 14, address := .fourth 1 5 2, method := .sixRegion, rotationLocalIds := ![15, 38, 19], zDenominator := 83333333333333250000000000000, zCounts := [15210465864000779194806168778, 52912220801487350048899300981, 15210646667845120756294530241, 0, 0] },
  { objectId := 91, sourceIndex := 84, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![85, 86, 87], zDenominator := 1000000000000000000000000000000, zCounts := [21324755035679813424936819123, 957349692816884446718981081842, 21325552147435739856082099035] },
  { objectId := 92, sourceIndex := 85, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![86, 87, 85], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 93, sourceIndex := 86, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![87, 85, 86], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 154, sourceIndex := 15, address := .fourth 1 6 1, method := .sixRegion, rotationLocalIds := ![16, 41, 11], zDenominator := 125000000000000000000000000000, zCounts := [62499979606570107844791543747, 62500020393429892155208456253, 0, 0, 0] },
  { objectId := 155, sourceIndex := 16, address := .fourth 1 7 0, method := .leGallBoundary, rotationLocalIds := ![17, 43, 2], zDenominator := 1, zCounts := [1, 0, 0, 0, 0] },
  { objectId := 156, sourceIndex := 17, address := .fourth 2 0 6, method := .leGallBoundary, rotationLocalIds := ![18, 7, 42], zDenominator := 333333333333333, zCounts := [0, 0, 69597571334804, 194138190660608, 69597571337921] },
  { objectId := 34, sourceIndex := 27, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![28, 29, 30], zDenominator := 1000000000000000, zCounts := [37200136513905, 925599726985811, 37200136500284] },
  { objectId := 94, sourceIndex := 87, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![88, 89, 90], zDenominator := 33333333333333300000000000000000000000000000, zCounts := [6590771925334057848982271593868009371617, 33320151138827801991478886420874296097501464, 6591422580163950672131307531835893126919] },
  { objectId := 95, sourceIndex := 88, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![89, 90, 88], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 36, sourceIndex := 29, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![30, 28, 29], zDenominator := 1000000000000000, zCounts := [403454714759561, 193090573085681, 403454712154758] },
  { objectId := 96, sourceIndex := 89, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![90, 88, 89], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 35, sourceIndex := 28, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![29, 30, 28], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 157, sourceIndex := 18, address := .fourth 2 1 5, method := .sixRegion, rotationLocalIds := ![19, 15, 38], zDenominator := 1000000000000000000000000000000, zCounts := [0, 1391630958173011920935089105, 498608739167650629785623212965, 498607981201181818955886747224, 1391648672994539337554950706] },
  { objectId := 37, sourceIndex := 30, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![31, 32, 33], zDenominator := 1000000000000000, zCounts := [43205437446463, 913589124530632, 43205438022905] },
  { objectId := 97, sourceIndex := 90, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![91, 92, 93], zDenominator := 999999999999999000000000000000000000000000000, zCounts := [5529096912553164912092187230601947012692904, 988941792964391868934185678204020855515802159, 5529110123053966153722134565377197471504937] },
  { objectId := 98, sourceIndex := 91, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![92, 93, 91], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 39, sourceIndex := 32, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![33, 31, 32], zDenominator := 500000000000000, zCounts := [27603813274839, 444792385226705, 27603801498456] },
  { objectId := 99, sourceIndex := 92, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![93, 91, 92], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 38, sourceIndex := 31, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![32, 33, 31], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 158, sourceIndex := 19, address := .fourth 2 2 4, method := .sixRegion, rotationLocalIds := ![20, 22, 33], zDenominator := 1000000000000000000000000000000, zCounts := [15323329413099431755145615, 72025157105844115992386733216, 855919052397413832790945047167, 72025143809587818937469547462, 15323357741132847443526540] },
  { objectId := 40, sourceIndex := 33, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![34, 35, 36], zDenominator := 1000000000000000, zCounts := [52872504103269, 894255111759066, 52872384137665] },
  { objectId := 100, sourceIndex := 93, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![94, 95, 96], zDenominator := 33333333333333300000000000000000000000000000, zCounts := [202142479346071178488146916228652026334338, 32929049890657191386398176089001859168691555, 202140963330037435113676994769488804974107] },
  { objectId := 101, sourceIndex := 94, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![95, 96, 94], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 42, sourceIndex := 35, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![36, 34, 35], zDenominator := 1000000000000000, zCounts := [57051511088545, 885896840599424, 57051648312031] },
  { objectId := 102, sourceIndex := 95, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![96, 94, 95], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 41, sourceIndex := 34, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![35, 36, 34], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 159, sourceIndex := 20, address := .fourth 2 3 3, method := .sixRegion, rotationLocalIds := ![21, 28, 27], zDenominator := 1000000000000000000000000000000, zCounts := [13192362190529580009966731842, 486808047277958900636329439890, 486807331691562801506089470753, 13192258839948717847614357515, 0] },
  { objectId := 43, sourceIndex := 36, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![37, 38, 39], zDenominator := 1000000000000000, zCounts := [55265633936126, 889468731626683, 55265634437191] },
  { objectId := 103, sourceIndex := 96, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![97, 98, 99], zDenominator := 28571428571428599999999999999971428571428571400000000000000, zCounts := [156697109711189059503263477338745998154168222674313119393, 28258034360719948399043572613219156946077339590002020554054, 156697100997462541453163909413525627197063587323666326553] },
  { objectId := 104, sourceIndex := 97, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![98, 99, 97], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 45, sourceIndex := 38, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![39, 37, 38], zDenominator := 1000000000000001, zCounts := [43587809900576, 912824379832484, 43587810266941] },
  { objectId := 105, sourceIndex := 98, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![99, 97, 98], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 44, sourceIndex := 37, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![38, 39, 37], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 160, sourceIndex := 21, address := .fourth 2 4 2, method := .sixRegion, rotationLocalIds := ![22, 33, 20], zDenominator := 1000000000000000000000000000000, zCounts := [183435042223508849856495343466, 633130268559012074863130913811, 183434689217479075280373742723, 0, 0] },
  { objectId := 46, sourceIndex := 39, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![40, 41, 42], zDenominator := 333333333333333, zCounts := [111111111053069, 111111111227195, 111111111053069] },
  { objectId := 106, sourceIndex := 99, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![100, 101, 102], zDenominator := 999999999999999000000000000000000000000000000, zCounts := [49573454900481394378048606586918445675513, 999900856168280553908256945079732382196266510, 49570376817964697365006313680699358057977] },
  { objectId := 107, sourceIndex := 100, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![101, 102, 100], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 48, sourceIndex := 41, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![42, 40, 41], zDenominator := 1000000000000000, zCounts := [37628947587229, 924742103982061, 37628948430710] },
  { objectId := 108, sourceIndex := 101, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![102, 100, 101], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 47, sourceIndex := 40, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![41, 42, 40], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 161, sourceIndex := 22, address := .fourth 2 5 1, method := .sixRegion, rotationLocalIds := ![23, 37, 12], zDenominator := 1000000000000001000000000000000, zCounts := [499999999999055601905926078983, 500000000000945398094073921017, 0, 0, 0] },
  { objectId := 162, sourceIndex := 23, address := .fourth 2 6 0, method := .leGallBoundary, rotationLocalIds := ![24, 40, 3], zDenominator := 1, zCounts := [1, 0, 0, 0, 0] },
  { objectId := 163, sourceIndex := 24, address := .fourth 3 0 5, method := .leGallBoundary, rotationLocalIds := ![25, 6, 39], zDenominator := 1000000000000000, zCounts := [0, 26998974945047, 473001176963099, 473000887068939, 26998961022915] },
  { objectId := 49, sourceIndex := 42, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![43, 44, 45], zDenominator := 1000000000000001, zCounts := [38922930458559, 922154139210089, 38922930331353] },
  { objectId := 109, sourceIndex := 102, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![103, 104, 105], zDenominator := 1000000000000002000000000000001000000000000000, zCounts := [889377918366566447140405097991149553916271, 998221242082679634656204863464965296142425935, 889379998955798896654731438043554303657794] },
  { objectId := 110, sourceIndex := 103, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![104, 105, 103], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 51, sourceIndex := 44, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![45, 43, 44], zDenominator := 1000000000000000, zCounts := [48173101127298, 903653799320607, 48173099552095] },
  { objectId := 111, sourceIndex := 104, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![105, 103, 104], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 50, sourceIndex := 43, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![44, 45, 43], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 164, sourceIndex := 25, address := .fourth 3 1 4, method := .sixRegion, rotationLocalIds := ![26, 14, 34], zDenominator := 1000000000000001000000000000000, zCounts := [15442111259735528446588818, 72089780959954447101076181171, 855789542616644895197308058847, 72089792175889484855635137262, 15442136252437317534033902] },
  { objectId := 52, sourceIndex := 45, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![46, 47, 48], zDenominator := 999999999999999, zCounts := [52893037829213, 894214128137930, 52892834032856] },
  { objectId := 112, sourceIndex := 105, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![106, 107, 108], zDenominator := 333333333333333000000000000000000000000000000, zCounts := [1995637777862576011831264366916426377014317, 329342062514438445907012954307250569793546162, 1995633041031978081155781325833003829439521] },
  { objectId := 113, sourceIndex := 106, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![107, 108, 106], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 54, sourceIndex := 47, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![48, 46, 47], zDenominator := 1000000000000000, zCounts := [57152352354681, 885695321145251, 57152326500068] },
  { objectId := 114, sourceIndex := 107, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![108, 106, 107], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 53, sourceIndex := 46, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![47, 48, 46], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 165, sourceIndex := 26, address := .fourth 3 2 3, method := .sixRegion, rotationLocalIds := ![27, 21, 28], zDenominator := 1000000000000000000000000000000, zCounts := [13132303930840513093638902826, 486867529943998775058158721588, 486867886232516212456172802005, 13132279892644499392029573581, 0] },
  { objectId := 55, sourceIndex := 48, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![49, 50, 51], zDenominator := 500000000000000, zCounts := [28537703935299, 442924576329475, 28537719735226] },
  { objectId := 115, sourceIndex := 108, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![109, 110, 111], zDenominator := 1000000000000001000000000000000000000000000000, zCounts := [5990633138975434663026307503365065232166953, 988018618855911972256847043410274873341573071, 5990748005113593080126649086360061426259976] },
  { objectId := 116, sourceIndex := 109, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![110, 111, 109], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 57, sourceIndex := 50, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![51, 49, 50], zDenominator := 1000000000000000, zCounts := [52899054671426, 894201970007713, 52898975320861] },
  { objectId := 117, sourceIndex := 110, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![111, 109, 110], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 56, sourceIndex := 49, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![50, 51, 49], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 166, sourceIndex := 27, address := .fourth 3 3 2, method := .sixRegion, rotationLocalIds := ![28, 27, 21], zDenominator := 500000000000000000000000000000, zCounts := [91122035477309633947782724420, 317755985551322833678736110839, 91121978971367532373481164741, 0, 0] },
  { objectId := 58, sourceIndex := 51, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![52, 53, 54], zDenominator := 1000000000000000, zCounts := [48188699360936, 903622601140799, 48188699498265] },
  { objectId := 118, sourceIndex := 111, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![112, 113, 114], zDenominator := 55555555555555555555555555555500000000000000000000000000000, zCounts := [46379262726869561294106004898703213783736766928471998786, 55462797029595334517480004630777232561181472577367060539807, 46379263233351476781444919824064225034790655704467461407] },
  { objectId := 119, sourceIndex := 112, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![113, 114, 112], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 60, sourceIndex := 53, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![54, 52, 53], zDenominator := 1000000000000000, zCounts := [39309181482517, 921381637035301, 39309181482182] },
  { objectId := 120, sourceIndex := 113, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![114, 112, 113], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 59, sourceIndex := 52, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![53, 54, 52], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 167, sourceIndex := 28, address := .fourth 3 4 1, method := .sixRegion, rotationLocalIds := ![29, 32, 13], zDenominator := 3125000000000000000000000000, zCounts := [1562500000023689218576797833, 1562499999976310781423202167, 0, 0, 0] },
  { objectId := 168, sourceIndex := 29, address := .fourth 3 5 0, method := .leGallBoundary, rotationLocalIds := ![30, 36, 4], zDenominator := 1, zCounts := [1, 0, 0, 0, 0] },
  { objectId := 169, sourceIndex := 30, address := .fourth 4 0 4, method := .leGallBoundary, rotationLocalIds := ![31, 5, 35], zDenominator := 1000000000000000, zCounts := [2425576305266, 130946280672485, 733256247635908, 130946319156039, 2425576230302] },
  { objectId := 61, sourceIndex := 54, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![55, 56, 57], zDenominator := 1000000000000000, zCounts := [48188147199271, 903623705460121, 48188147340608] },
  { objectId := 121, sourceIndex := 114, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![115, 116, 117], zDenominator := 38461538461538500000000000000000000000000000, zCounts := [32160653719528602886053425709858127202779, 38397217153381367084935792329273945992649710, 32160654437604312178154245016195880147511] },
  { objectId := 122, sourceIndex := 115, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![116, 117, 115], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 63, sourceIndex := 56, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![57, 55, 56], zDenominator := 500000000000000, zCounts := [19656752067590, 460686495865381, 19656752067029] },
  { objectId := 123, sourceIndex := 116, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![117, 115, 116], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 62, sourceIndex := 55, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![56, 57, 55], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 170, sourceIndex := 31, address := .fourth 4 1 3, method := .sixRegion, rotationLocalIds := ![32, 13, 29], zDenominator := 500000000000000000000000000000, zCounts := [6543966019668374766564501313, 243456059521217005138142691682, 243456006301333185251089634118, 6543968157781434844203172887, 0] },
  { objectId := 64, sourceIndex := 57, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![58, 59, 60], zDenominator := 1000000000000000, zCounts := [55269512449195, 889460974713096, 55269512837709] },
  { objectId := 124, sourceIndex := 117, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![118, 119, 120], zDenominator := 11363636363636375000000000000000000000000000, zCounts := [62268597247740629448091148262114762350075, 11239099172234634447955123745550114095695396, 62268594153999922596785106187771141954529] },
  { objectId := 125, sourceIndex := 118, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![119, 120, 118], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 66, sourceIndex := 59, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![60, 58, 59], zDenominator := 999999999999999, zCounts := [43583834711735, 912832330529485, 43583834758779] },
  { objectId := 126, sourceIndex := 119, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![120, 118, 119], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 65, sourceIndex := 58, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![59, 60, 58], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 171, sourceIndex := 32, address := .fourth 4 2 2, method := .sixRegion, rotationLocalIds := ![33, 20, 22], zDenominator := 500000000000000000000000000000, zCounts := [90968735384104925259032514224, 318062524950241058873984501585, 90968739665654015866982984191, 0, 0] },
  { objectId := 67, sourceIndex := 60, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![61, 62, 63], zDenominator := 1000000000000000, zCounts := [39309211984339, 921381570625483, 39309217390178] },
  { objectId := 127, sourceIndex := 120, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![121, 122, 123], zDenominator := 999999999999999000000000000000000000000000000, zCounts := [834177965614025051517273716997229200268025, 998331713943758569755129745523073023112145558, 834108090626405193352980759929747687586417] },
  { objectId := 128, sourceIndex := 121, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![122, 123, 121], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 69, sourceIndex := 62, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![63, 61, 62], zDenominator := 200000000000000, zCounts := [9637765145873, 180724461156025, 9637773698102] },
  { objectId := 129, sourceIndex := 122, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![123, 121, 122], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 68, sourceIndex := 61, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![62, 63, 61], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 172, sourceIndex := 33, address := .fourth 4 3 1, method := .sixRegion, rotationLocalIds := ![34, 26, 14], zDenominator := 142857142857143000000000000000, zCounts := [71428571428038743380508787683, 71428571429104256619491212317, 0, 0, 0] },
  { objectId := 173, sourceIndex := 34, address := .fourth 4 4 0, method := .leGallBoundary, rotationLocalIds := ![35, 31, 5], zDenominator := 1, zCounts := [1, 0, 0, 0, 0] },
  { objectId := 174, sourceIndex := 35, address := .fourth 5 0 3, method := .leGallBoundary, rotationLocalIds := ![36, 4, 30], zDenominator := 1000000000000001, zCounts := [21932170849084, 478068039533261, 478067599777759, 21932189839897, 0] },
  { objectId := 70, sourceIndex := 63, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![64, 65, 66], zDenominator := 1000000000000000, zCounts := [405428415388205, 189143166661914, 405428417949881] },
  { objectId := 130, sourceIndex := 123, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![124, 125, 126], zDenominator := 1000000000000002000000000000001000000000000000, zCounts := [38466184181158088176307154246782992104378, 999923069840846170215566321418786744862704245, 38463974974671696257371427966472145191377] },
  { objectId := 131, sourceIndex := 124, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![125, 126, 124], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 72, sourceIndex := 65, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![66, 64, 65], zDenominator := 500000000000000, zCounts := [18813898207999, 462372203554262, 18813898237739] },
  { objectId := 132, sourceIndex := 125, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![126, 124, 125], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 71, sourceIndex := 64, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![65, 66, 64], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 175, sourceIndex := 36, address := .fourth 5 1 2, method := .sixRegion, rotationLocalIds := ![37, 12, 23], zDenominator := 1000000000000000000000000000000, zCounts := [182504178883141869154180135523, 634992871318010940641369847427, 182502949798847190204450017050, 0, 0] },
  { objectId := 73, sourceIndex := 66, address := .square 0 2 2, method := .leGallBoundary, rotationLocalIds := ![67, 68, 69], zDenominator := 1000000000000000, zCounts := [37630089893749, 924739822340272, 37630087765979] },
  { objectId := 133, sourceIndex := 126, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![127, 128, 129], zDenominator := 999999999999999999999999999999000000000000000, zCounts := [31722077991530522285512622979471969830537, 999936208714213915708755739937652396551883526, 32069207794553768958747438368131478285937] },
  { objectId := 134, sourceIndex := 127, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![128, 129, 127], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 75, sourceIndex := 68, address := .square 2 0 2, method := .leGallBoundary, rotationLocalIds := ![69, 67, 68], zDenominator := 1000000000000000, zCounts := [333333333177518, 333333333644965, 333333333177517] },
  { objectId := 135, sourceIndex := 128, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![129, 127, 128], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 74, sourceIndex := 67, address := .square 2 2 0, method := .leGallBoundary, rotationLocalIds := ![68, 69, 67], zDenominator := 1, zCounts := [1, 0, 0] },
  { objectId := 176, sourceIndex := 37, address := .fourth 5 2 1, method := .sixRegion, rotationLocalIds := ![38, 19, 15], zDenominator := 500000000000000000000000000000, zCounts := [249999999999980545072377698427, 250000000000019454927622301573, 0, 0, 0] },
  { objectId := 177, sourceIndex := 38, address := .fourth 5 3 0, method := .leGallBoundary, rotationLocalIds := ![39, 25, 6], zDenominator := 1, zCounts := [1, 0, 0, 0, 0] },
  { objectId := 178, sourceIndex := 39, address := .fourth 6 0 2, method := .leGallBoundary, rotationLocalIds := ![40, 3, 24], zDenominator := 1000000000000000, zCounts := [169434127137797, 661133700988730, 169432171873473, 0, 0] },
  { objectId := 136, sourceIndex := 129, address := .square 1 1 2, method := .leGallInteriorUnique, rotationLocalIds := ![130, 131, 132], zDenominator := 999999999999999000000000000000, zCounts := [21291423707147060962270522171, 957417241475000376547582763023, 21291334817851562490146714806] },
  { objectId := 137, sourceIndex := 130, address := .square 1 2 1, method := .leGallInteriorUnique, rotationLocalIds := ![131, 132, 130], zDenominator := 500000000000000000000000000000, zCounts := [249999999468025350391953735523, 250000000531974649608046264477, 0] },
  { objectId := 138, sourceIndex := 131, address := .square 2 1 1, method := .leGallInteriorUnique, rotationLocalIds := ![132, 130, 131], zDenominator := 18518518518518500000000000000000000000000000, zCounts := [9259259236978132563845180469335159119718943, 9259259281540367436154819530664840880281057, 0] },
  { objectId := 179, sourceIndex := 40, address := .fourth 6 1 1, method := .sixRegion, rotationLocalIds := ![41, 11, 16], zDenominator := 6250000000000000000000000000, zCounts := [3124998782023817913559871079, 3125001217976182086440128921, 0, 0, 0] },
  { objectId := 180, sourceIndex := 41, address := .fourth 6 2 0, method := .leGallBoundary, rotationLocalIds := ![42, 18, 7], zDenominator := 1, zCounts := [1, 0, 0, 0, 0] },
  { objectId := 181, sourceIndex := 42, address := .fourth 7 0 1, method := .leGallBoundary, rotationLocalIds := ![43, 2, 17], zDenominator := 1000000000000000, zCounts := [499999999026019, 500000000973981, 0, 0, 0] },
  { objectId := 182, sourceIndex := 43, address := .fourth 7 1 0, method := .leGallBoundary, rotationLocalIds := ![44, 10, 8], zDenominator := 1, zCounts := [1, 0, 0, 0, 0] },
  { objectId := 183, sourceIndex := 44, address := .fourth 8 0 0, method := .leGallBoundary, rotationLocalIds := ![45, 1, 9], zDenominator := 1, zCounts := [1, 0, 0, 0, 0] }
]

theorem componentMetadata_size : componentMetadata.size = 180 := by
  decide +kernel

def ComponentAddress.shapeSum : ComponentAddress → Nat
  | .base i j k | .square i j k | .fourth i j k =>
      i.val + j.val + k.val

def ComponentAddress.zWidth : ComponentAddress → Nat
  | .base .. => 2
  | .square .. => 3
  | .fourth .. => 5

def ComponentMetadata.valid (metadata : ComponentMetadata) : Bool :=
  match metadata.address with
  | .base i j k => decide (
      i.val + j.val + k.val = 2 ∧ metadata.sourceIndex < 6 ∧
      metadata.objectId = metadata.sourceIndex + 1 ∧
      ∀ r, 0 < metadata.rotationLocalIds r ∧
        metadata.rotationLocalIds r ≤ 6) &&
      decide (metadata.zDenominator = 1 ∧
        metadata.zCounts.length = 2 ∧ metadata.zCounts.sum = 0)
  | .square i j k => decide (
      i.val + j.val + k.val = 4 ∧ metadata.sourceIndex < 132 ∧
      metadata.objectId = metadata.sourceIndex + 7 ∧
      ∀ r, 0 < metadata.rotationLocalIds r ∧
        metadata.rotationLocalIds r ≤ 132) &&
      decide (0 < metadata.zDenominator ∧
        metadata.zCounts.length = 3 ∧
        metadata.zCounts.sum = metadata.zDenominator)
  | .fourth i j k => decide (
      i.val + j.val + k.val = 8 ∧ metadata.sourceIndex < 45 ∧
      metadata.objectId = metadata.sourceIndex + 139 ∧
      ∀ r, 0 < metadata.rotationLocalIds r ∧
        metadata.rotationLocalIds r ≤ 45) &&
      decide (0 < metadata.zDenominator ∧
        metadata.zCounts.length = 5 ∧
        metadata.zCounts.sum = metadata.zDenominator)

/-- Exact rational Z-profile selected by the recursive replay. -/
def ComponentMetadata.zProbability (metadata : ComponentMetadata)
    (index : Nat) : Rat :=
  ((metadata.zCounts[index]?.getD 0 : Nat) : Rat) /
    (metadata.zDenominator : Rat)

/-- Typed count function consumed directly by an
`IntegerZSplitProfile metadata.address.zWidth`. -/
def ComponentMetadata.zCount (metadata : ComponentMetadata)
    (index : Fin metadata.address.zWidth) : Nat :=
  metadata.zCounts[index.val]?.getD 0

def componentSpecAt (index : Fin 180) : ComponentMetadata :=
  componentMetadata[index.val]'(by
    rw [componentMetadata_size]
    exact index.isLt)

def componentObjectIds : List Nat :=
  componentMetadata.toList.map ComponentMetadata.objectId

/-- Source object 184 is the global fourth-power node appended after
the 180 reachable component/profile records. -/
def globalSourceObjectId : Nat := 184

def ledgerObjectId (index : Fin 181) : Nat :=
  if h : index.val < 180 then
    (componentSpecAt ⟨index.val, h⟩).objectId
  else globalSourceObjectId

/-- The exact public tensor constructors missing from the compact
workspace.  In the authoritative library these fields instantiate as
the canonical blocks of `CWObj K 5`, `cwSquareCanonicalGrading K 5`,
and `StothersFourth.cwFourthCanonicalGrading K 5`. -/
structure Q5CanonicalComponents (K : Type u) [Field K] where
  cwObj5 : TensorObj K 3
  kron : TensorObj K 3 → TensorObj K 3 → TensorObj K 3
  cwBlock5 : Fin 3 → Fin 3 → Fin 3 → TensorObj K 3
  cwSquareBlock5 : Fin 5 → Fin 5 → Fin 5 → TensorObj K 3
  cwFourthBlock5 : Fin 9 → Fin 9 → Fin 9 → TensorObj K 3

namespace Q5CanonicalComponents

variable {K : Type u} [Field K]

noncomputable def component (api : Q5CanonicalComponents K) :
    ComponentAddress → TensorObj K 3
  | .base i j k => api.cwBlock5 i j k
  | .square i j k => api.cwSquareBlock5 i j k
  | .fourth i j k => api.cwFourthBlock5 i j k

/-- The literal parenthesized fourth power used by the public
`StothersFourth.cwFourthObj K 5` definition. -/
noncomputable def cwFourthObj5 (api : Q5CanonicalComponents K) :
    TensorObj K 3 :=
  api.kron (api.kron api.cwObj5 api.cwObj5)
    (api.kron api.cwObj5 api.cwObj5)

end Q5CanonicalComponents

/-- Data-driven tensor family in exactly the scalar-ledger order.
Indices below 180 are canonical component blocks; index 180 is the
literal whole fourth power. -/
noncomputable def tensorAt {K : Type u} [Field K]
    (api : Q5CanonicalComponents K) (index : Fin 181) : TensorObj K 3 :=
  if h : index.val < 180 then
    api.component (componentSpecAt ⟨index.val, h⟩).address
  else api.cwFourthObj5

def componentLedgerIndex (index : Fin 180) : Fin 181 :=
  ⟨index.val, Nat.lt_trans index.isLt (by norm_num)⟩

end MME.DWZFourthTensorLedger


