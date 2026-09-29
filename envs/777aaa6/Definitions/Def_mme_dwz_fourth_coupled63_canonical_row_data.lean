-- Prove2me | Definitions.Def_mme_dwz_fourth_coupled63_canonical_row_data
-- name    : mme_dwz_fourth_coupled63_canonical_row_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-16T08:27:39.41885+00:00
-- url     : https://prove2.me/theorems/a5fe2a7c-21ee-4eaa-b20a-5a726344855a
-- title:
--   Exact canonicalized data for sixty-three q=5 coupled square-component rows
-- statement:
--   This fixed data table records the 63 coupled square-component entries of the local q=5 fourth-power ledger, with original ledger indices, object identifiers, literal addresses 112/121/211, positive integer parameters l,g, and exact rational logarithmic rates. The literal 112 profiles have counts (l,2g,l) and denominator 2(l+g). The 121/211 profiles have counts (l+g,l+g,0) with the same denominator. These are canonicalized profiles, not a claim that the original numerical profiles are unchanged: nonexceptional 112 rows average their edge counts, object 76 is retuned to l=1,g=4, and all directional rows use l=21,g=479. The data do not assert compatibility of those replacements with a larger parent tensor assembly.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5, Definition 3.9, Lemma 4.6(d), and Appendix A. Exact canonicalized rational component data for the local q=5 fourth-power certificate; ledger indices and object identifiers are formalization bookkeeping, not paper numbering.

import Definitions.Def_mme_complete_split_canonical_square_data
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open BigOperators MME MME.DWZRestrictedValue

namespace MME.Coupled63Scalar

structure Row where
  ledgerIndex : ℕ
  objectId : ℕ
  address : Fin 3 → ℕ
  l : ℕ
  g : ℕ
  rate : ℚ

def rows : Fin 63 → Row := ![
  { ledgerIndex := 28, objectId := 76, address := ![1, 1, 2], l := 1, g := 4, rate := (2661713696819 / 1000000000000 : ℚ) },
  { ledgerIndex := 29, objectId := 77, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 30, objectId := 78, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 33, objectId := 79, address := ![1, 1, 2], l := 91875149636298293671007557816071292692811, g := 249908124850363951706328992442183928707307189, rate := (1503893725497 / 500000000000 : ℚ) },
  { ledgerIndex := 34, objectId := 80, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 36, objectId := 81, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 40, objectId := 82, address := ![1, 1, 2], l := 887578005182547226714082561, g := 499112421994817952773285917439, rate := (3009569226233 / 1000000000000 : ℚ) },
  { ledgerIndex := 41, objectId := 83, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 43, objectId := 84, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 47, objectId := 85, address := ![1, 1, 2], l := 835920710211032919992128345247667378096023, g := 499164079289789467080007871654752332621903977, rate := (1504728865951 / 500000000000 : ℚ) },
  { ledgerIndex := 48, objectId := 86, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 50, objectId := 87, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 54, objectId := 88, address := ![1, 1, 2], l := 82066877672188036469111593136413219835891, g := 999917933122326811963530888406863586780164109, rate := (601455624323 / 200000000000 : ℚ) },
  { ledgerIndex := 55, objectId := 89, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 57, objectId := 90, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 60, objectId := 91, address := ![1, 1, 2], l := 42650307183115553281018918158, g := 957349692816884446718981081842, rate := (755355109047 / 250000000000 : ℚ) },
  { ledgerIndex := 61, objectId := 92, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 62, objectId := 93, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 67, objectId := 94, address := ![1, 1, 2], l := 13182194505498008521113579125703902498536, g := 33320151138827801991478886420874296097501464, rate := (1503915850307 / 500000000000 : ℚ) },
  { ledgerIndex := 68, objectId := 95, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 70, objectId := 96, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 74, objectId := 97, address := ![1, 1, 2], l := 11058207035607131065814321795979144484197841, g := 988941792964391868934185678204020855515802159, rate := (3015832291319 / 1000000000000 : ℚ) },
  { ledgerIndex := 75, objectId := 98, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 77, objectId := 99, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 81, objectId := 100, address := ![1, 1, 2], l := 404283442676108613601823910998140831308445, g := 32929049890657191386398176089001859168691555, rate := (754075958133 / 250000000000 : ℚ) },
  { ledgerIndex := 82, objectId := 101, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 84, objectId := 102, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 88, objectId := 103, address := ![1, 1, 2], l := 313394210708651600956427386752271625351231809997979445946, g := 28258034360719948399043572613219156946077339590002020554054, rate := (3015791363853 / 1000000000000 : ℚ) },
  { ledgerIndex := 89, objectId := 104, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 91, objectId := 105, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 95, objectId := 106, address := ![1, 1, 2], l := 99143831718446091743054920267617803733490, g := 999900856168280553908256945079732382196266510, rate := (1503656667397 / 500000000000 : ℚ) },
  { ledgerIndex := 96, objectId := 107, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 98, objectId := 108, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 104, objectId := 109, address := ![1, 1, 2], l := 1778757917322365343795136536034703857574065, g := 998221242082679634656204863464965296142425935, rate := (3009573076393 / 1000000000000 : ℚ) },
  { ledgerIndex := 105, objectId := 110, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 107, objectId := 111, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 111, objectId := 112, address := ![1, 1, 2], l := 3991270818894554092987045692749430206453838, g := 329342062514438445907012954307250569793546162, rate := (94257428723 / 31250000000 : ℚ) },
  { ledgerIndex := 112, objectId := 113, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 114, objectId := 114, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 118, objectId := 115, address := ![1, 1, 2], l := 11981381144089027743152956589725126658426929, g := 988018618855911972256847043410274873341573071, rate := (3016240969539 / 1000000000000 : ℚ) },
  { ledgerIndex := 119, objectId := 116, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 121, objectId := 117, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 125, objectId := 118, address := ![1, 1, 2], l := 92758525960221038075550924722767438818527422632939460193, g := 55462797029595334517480004630777232561181472577367060539807, rate := (3009455348119 / 1000000000000 : ℚ) },
  { ledgerIndex := 126, objectId := 119, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 128, objectId := 120, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 134, objectId := 121, address := ![1, 1, 2], l := 64321308157132915064207670726054007350290, g := 38397217153381367084935792329273945992649710, rate := (1504729145117 / 500000000000 : ℚ) },
  { ledgerIndex := 135, objectId := 122, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 137, objectId := 123, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 141, objectId := 124, address := ![1, 1, 2], l := 124537191401740552044876254449885904304604, g := 11239099172234634447955123745550114095695396, rate := (94243343423 / 31250000000 : ℚ) },
  { ledgerIndex := 142, objectId := 125, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 144, objectId := 126, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 148, objectId := 127, address := ![1, 1, 2], l := 1668286056240430244870254476926976887854442, g := 998331713943758569755129745523073023112145558, rate := (601890771567 / 200000000000 : ℚ) },
  { ledgerIndex := 149, objectId := 128, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 151, objectId := 129, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 157, objectId := 130, address := ![1, 1, 2], l := 76930159155829784433678582213255137295755, g := 999923069840846170215566321418786744862704245, rate := (3007267307853 / 1000000000000 : ℚ) },
  { ledgerIndex := 158, objectId := 131, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 160, objectId := 132, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 164, objectId := 133, address := ![1, 1, 2], l := 63791285786084291244260061347603448116474, g := 999936208714213915708755739937652396551883526, rate := (30072391073 / 10000000000 : ℚ) },
  { ledgerIndex := 165, objectId := 134, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 167, objectId := 135, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) },
  { ledgerIndex := 172, objectId := 136, address := ![1, 1, 2], l := 42582758524998623452417236977, g := 957417241475000376547582763023, rate := (23604849337 / 7812500000 : ℚ) },
  { ledgerIndex := 173, objectId := 137, address := ![1, 2, 1], l := 21, g := 479, rate := (75535540347 / 25000000000 : ℚ) },
  { ledgerIndex := 174, objectId := 138, address := ![2, 1, 1], l := 21, g := 479, rate := (3021421613803 / 1000000000000 : ℚ) }]

def frequency (i : Fin 63) (a : Fin 3) : ℚ :=
  (![((rows i).l : ℚ), 2 * ((rows i).g : ℚ), ((rows i).l : ℚ)] a) /
    (2 * ((rows i).l + (rows i).g))


def logCoefficient (i : Fin 63) : ℚ :=
  (2 * ((rows i).g : ℚ) + (rows i).l) / ((rows i).l + (rows i).g)


def rho (i : Fin 63) : Fin 3 → Fin 5 :=
  if (rows i).address 2 = 2 then cwSquareBlockType 1 1 2
  else if (rows i).address 0 = 2 then cwSquareBlockType 2 1 1
  else cwSquareBlockType 1 2 1

def profile (i : Fin 63) : IntegerZSplitProfile 3 where
  denominator := 2 * ((rows i).l + (rows i).g)
  denominator_pos := by decide +kernel +revert
  count := if (rows i).address 2 = 2 then
    ![(rows i).l, 2 * (rows i).g, (rows i).l]
    else ![(rows i).l + (rows i).g, (rows i).l + (rows i).g, 0]
  count_sum := by decide +kernel +revert


end MME.Coupled63Scalar


