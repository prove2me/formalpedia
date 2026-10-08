-- Prove2me | Definitions.Def_GoldbachActiveRoundedData
-- name    : GoldbachActiveRoundedData
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-05T03:12:50.303723+00:00
-- url     : https://prove2.me/theorems/7427b8be-42c4-479c-9cff-dc89e1aefb6d
-- title:
--   Conservative integer data for all active and scalar packet certificates
-- statement:
--   Conservative integer data for all 63 active packet rows and the aligned scalar
--   row of the v4 release at https://goldbach-nine.vercel.app/ . The frozen
--   `active-scalar-witness.json` has SHA-256
--   `4c5a5d59a074253933d1efb7161bd69ae4656eed1dc70b9e21c5cedfb8cccc84`.
--
--   Set $D=10^{12}$. Every cap and mass budget is rounded upward to an integer
--   multiple of $D^{-1}$. Each finite cap prefix covers its rounded budget. The
--   constant tail is the last prefix cap, conservatively enlarging every omitted
--   source cap. Each active row additionally records its supplied low-class energy
--   rounded upward to a multiple of $D^{-2}$. The aligned scalar row has base
--   energy zero. Three distinguished scalar rows store their four independently
--   upward-rounded ingredients.
--
--   This definition is candidate numerical data, not a theorem about zeros or primes.
--   An exact Python generator checks its correspondence to all 67 frozen source
--   rows, including the full row inventory and common coordinate order. Separate
--   Lean proofs check the integer conditions and bound arbitrary real inputs
--   satisfying these enlarged constraints. The analytic derivation of the original
--   caps, budgets, low-class energy, and scalar ingredients remains unverified.
--   No mathematical novelty or complete exceptional-set theorem is claimed.
-- source:
--   Conservative numerical certificate bounds for https://goldbach-nine.vercel.app/release/goldbach-exception-069697-certificate-v4.zip . Analytic input derivation remains separate; no mathematical novelty is claimed.

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.GetD
set_option autoImplicit false

namespace GoldbachActiveRoundedData

structure Row where
  rCaps : List ℕ
  tCaps : List ℕ
  rTail : ℕ
  tTail : ℕ
  rBudget : ℕ
  tBudget : ℕ
  prefixLength : ℕ
  baseEnergy : ℕ

def scale : ℕ := 1000000000000

-- Frozen witness row: a-11_20-14_25-m1k1
def row0 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 154172522044 ++ List.replicate 1 136652881772 ++ List.replicate 1 125900464449 ++ List.replicate 1 113420478561 ++ List.replicate 1 106412010631 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 87352847421 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 2 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 3 59033177370 ++ List.replicate 3 58350622743 ++ List.replicate 43 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 117938436343502292124892

-- Frozen witness row: a-11_20-14_25-m2k1
def row1 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 154172522044 ++ List.replicate 1 136652881772 ++ List.replicate 1 120784595348 ++ List.replicate 1 111045671764 ++ List.replicate 1 101928764812 ++ List.replicate 1 93394146827 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 1 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 2 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 2 59033177370 ++ List.replicate 4 58350622743 ++ List.replicate 48 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 189849473581903837584286

-- Frozen witness row: a-11_20-14_25-m2k2
def row2 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 154172522044 ++ List.replicate 1 136652881772 ++ List.replicate 1 120784595348 ++ List.replicate 1 111045671764 ++ List.replicate 1 101928764812 ++ List.replicate 1 93394146827 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 1 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 2 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 2 59033177370 ++ List.replicate 4 58350622743 ++ List.replicate 48 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 239118694632513247849424

-- Frozen witness row: a-11_25-9_20-m1k1
def row3 : Row where
  rCaps := List.replicate 9 160408574090 ++ List.replicate 1 145195940618 ++ List.replicate 1 133897885510 ++ List.replicate 1 123321427417 ++ List.replicate 1 113420478561 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 95475287379 ++ List.replicate 1 91347063351 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 2 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 2 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 3 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 4 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 4 62578758415 ++ List.replicate 5 61851528143 ++ List.replicate 5 61133478523 ++ List.replicate 6 60424485067 ++ List.replicate 7 59724425029 ++ List.replicate 8 59033177370 ++ List.replicate 9 58350622743
  tCaps := List.replicate 100 66553314396
  rTail := 58350622743
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 172553261515873733125446

-- Frozen witness row: a-11_25-9_20-m2k1
def row4 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 145195940618 ++ List.replicate 1 131187973717 ++ List.replicate 1 120784595348 ++ List.replicate 1 111045671764 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 3 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 5 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 6 60424485067 ++ List.replicate 6 59724425029 ++ List.replicate 8 59033177370 ++ List.replicate 10 58350622743 ++ List.replicate 7 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 317226349500247803542992

-- Frozen witness row: a-11_25-9_20-m2k2
def row5 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 145195940618 ++ List.replicate 1 131187973717 ++ List.replicate 1 120784595348 ++ List.replicate 1 111045671764 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 3 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 5 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 6 60424485067 ++ List.replicate 6 59724425029 ++ List.replicate 8 59033177370 ++ List.replicate 10 58350622743 ++ List.replicate 7 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 350694997049967746086123

-- Frozen witness row: a-12_25-49_100-m1k1
def row6 : Row where
  rCaps := List.replicate 9 160408574090 ++ List.replicate 1 142301140439 ++ List.replicate 1 131187973717 ++ List.replicate 1 120784595348 ++ List.replicate 1 111045671764 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 2 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 3 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 4 61851528143 ++ List.replicate 3 61133478523 ++ List.replicate 4 60424485067 ++ List.replicate 5 59724425029 ++ List.replicate 6 59033177370 ++ List.replicate 6 58350622743 ++ List.replicate 21 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 149143158589648479801727

-- Frozen witness row: a-12_25-49_100-m2k1
def row7 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 142301140439 ++ List.replicate 1 128522408602 ++ List.replicate 1 115834794727 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 93394146827 ++ List.replicate 1 89333479619 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 3 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 5 59724425029 ++ List.replicate 5 59033177370 ++ List.replicate 6 58350622743 ++ List.replicate 28 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 261102656433384549468276

-- Frozen witness row: a-12_25-49_100-m2k2
def row8 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 142301140439 ++ List.replicate 1 128522408602 ++ List.replicate 1 115834794727 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 93394146827 ++ List.replicate 1 89333479619 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 3 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 5 59724425029 ++ List.replicate 5 59033177370 ++ List.replicate 6 58350622743 ++ List.replicate 28 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 302888133096063019587757

-- Frozen witness row: a-13_25-53_100-m1k1
def row9 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 157264824936 ++ List.replicate 1 139453712567 ++ List.replicate 1 125900464449 ++ List.replicate 1 115834794727 ++ List.replicate 1 108709727779 ++ List.replicate 1 99742015550 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 83143201783 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 3 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 4 59724425029 ++ List.replicate 3 59033177370 ++ List.replicate 5 58350622743 ++ List.replicate 35 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 130008724010156481291516

-- Frozen witness row: a-13_25-53_100-m2k1
def row10 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 157264824936 ++ List.replicate 1 136652881772 ++ List.replicate 1 123321427417 ++ List.replicate 1 113420478561 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 3 61851528143 ++ List.replicate 2 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 4 59033177370 ++ List.replicate 3 58350622743 ++ List.replicate 42 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 216850974826519196039383

-- Frozen witness row: a-13_25-53_100-m2k2
def row11 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 157264824936 ++ List.replicate 1 136652881772 ++ List.replicate 1 123321427417 ++ List.replicate 1 113420478561 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 3 61851528143 ++ List.replicate 2 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 4 59033177370 ++ List.replicate 3 58350622743 ++ List.replicate 42 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 263790688622999399366368

-- Frozen witness row: a-14_25-57_100-m1k1
def row12 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 154172522044 ++ List.replicate 1 136652881772 ++ List.replicate 1 123321427417 ++ List.replicate 1 113420478561 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 2 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 3 59033177370 ++ List.replicate 3 58350622743 ++ List.replicate 45 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 114296039004969196028003

-- Frozen witness row: a-14_25-57_100-m2k1
def row13 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 154172522044 ++ List.replicate 1 133897885510 ++ List.replicate 1 120784595348 ++ List.replicate 1 108709727779 ++ List.replicate 1 101928764812 ++ List.replicate 1 93394146827 ++ List.replicate 1 87352847421 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 1 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 1 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 2 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 2 59724425029 ++ List.replicate 3 59033177370 ++ List.replicate 3 58350622743 ++ List.replicate 50 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 181844742988026043525565

-- Frozen witness row: a-14_25-57_100-m2k2
def row14 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 154172522044 ++ List.replicate 1 133897885510 ++ List.replicate 1 120784595348 ++ List.replicate 1 108709727779 ++ List.replicate 1 101928764812 ++ List.replicate 1 93394146827 ++ List.replicate 1 87352847421 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 1 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 1 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 2 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 2 59724425029 ++ List.replicate 3 59033177370 ++ List.replicate 3 58350622743 ++ List.replicate 50 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 231670091571783289604621

-- Frozen witness row: a-1_2-51_100-m1k1
def row15 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 157264824936 ++ List.replicate 1 142301140439 ++ List.replicate 1 128522408602 ++ List.replicate 1 118289277573 ++ List.replicate 1 108709727779 ++ List.replicate 1 101928764812 ++ List.replicate 1 95475287379 ++ List.replicate 1 91347063351 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 2 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 3 61851528143 ++ List.replicate 3 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 4 59724425029 ++ List.replicate 5 59033177370 ++ List.replicate 5 58350622743 ++ List.replicate 29 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 139094138734003983878405

-- Frozen witness row: a-1_2-51_100-m2k1
def row16 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 157264824936 ++ List.replicate 1 139453712567 ++ List.replicate 1 125900464449 ++ List.replicate 1 115834794727 ++ List.replicate 1 106412010631 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 87352847421 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 3 61851528143 ++ List.replicate 3 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 5 59033177370 ++ List.replicate 4 58350622743 ++ List.replicate 36 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 237674718152888689558879

-- Frozen witness row: a-1_2-51_100-m2k2
def row17 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 157264824936 ++ List.replicate 1 139453712567 ++ List.replicate 1 125900464449 ++ List.replicate 1 115834794727 ++ List.replicate 1 106412010631 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 87352847421 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 3 61851528143 ++ List.replicate 3 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 5 59033177370 ++ List.replicate 4 58350622743 ++ List.replicate 36 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 282365993768422845261710

-- Frozen witness row: a-21_50-43_100-m1k1
def row18 : Row where
  rCaps := List.replicate 9 160408574090 ++ List.replicate 1 148138901231 ++ List.replicate 1 133897885510 ++ List.replicate 1 123321427417 ++ List.replicate 1 115834794727 ++ List.replicate 1 108709727779 ++ List.replicate 1 101928764812 ++ List.replicate 1 97591051610 ++ List.replicate 1 93394146827 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 2 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 2 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 3 66357101294 ++ List.replicate 3 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 4 64061267691 ++ List.replicate 4 63315295587 ++ List.replicate 5 62578758415 ++ List.replicate 5 61851528143 ++ List.replicate 7 61133478523 ++ List.replicate 7 60424485067 ++ List.replicate 9 59724425029 ++ List.replicate 6 59033177370
  tCaps := List.replicate 100 66553314396
  rTail := 59033177370
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 186184143035489641163218

-- Frozen witness row: a-21_50-43_100-m2k1
def row19 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 145195940618 ++ List.replicate 1 131187973717 ++ List.replicate 1 120784595348 ++ List.replicate 1 113420478561 ++ List.replicate 1 104151894752 ++ List.replicate 1 99742015550 ++ List.replicate 1 93394146827 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 2 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 3 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 4 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 5 62578758415 ++ List.replicate 5 61851528143 ++ List.replicate 6 61133478523 ++ List.replicate 7 60424485067 ++ List.replicate 8 59724425029 ++ List.replicate 10 59033177370 ++ List.replicate 4 58350622743
  tCaps := List.replicate 100 66553314396
  rTail := 58350622743
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 350776975672145904835364

-- Frozen witness row: a-21_50-43_100-m2k2
def row20 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 145195940618 ++ List.replicate 1 131187973717 ++ List.replicate 1 120784595348 ++ List.replicate 1 113420478561 ++ List.replicate 1 104151894752 ++ List.replicate 1 99742015550 ++ List.replicate 1 93394146827 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 2 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 3 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 4 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 5 62578758415 ++ List.replicate 5 61851528143 ++ List.replicate 6 61133478523 ++ List.replicate 7 60424485067 ++ List.replicate 8 59724425029 ++ List.replicate 10 59033177370 ++ List.replicate 4 58350622743
  tCaps := List.replicate 100 66553314396
  rTail := 58350622743
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 378523695419161388380754

-- Frozen witness row: a-23_50-47_100-m1k1
def row21 : Row where
  rCaps := List.replicate 9 160408574090 ++ List.replicate 1 145195940618 ++ List.replicate 1 131187973717 ++ List.replicate 1 120784595348 ++ List.replicate 1 113420478561 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 93394146827 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 2 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 3 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 3 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 4 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 5 60424485067 ++ List.replicate 6 59724425029 ++ List.replicate 7 59033177370 ++ List.replicate 8 58350622743 ++ List.replicate 11 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 160249339676025311401194

-- Frozen witness row: a-23_50-47_100-m2k1
def row22 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 142301140439 ++ List.replicate 1 128522408602 ++ List.replicate 1 118289277573 ++ List.replicate 1 108709727779 ++ List.replicate 1 101928764812 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 4 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 4 60424485067 ++ List.replicate 5 59724425029 ++ List.replicate 6 59033177370 ++ List.replicate 8 58350622743 ++ List.replicate 19 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 287495664184190853941028

-- Frozen witness row: a-23_50-47_100-m2k2
def row23 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 142301140439 ++ List.replicate 1 128522408602 ++ List.replicate 1 118289277573 ++ List.replicate 1 108709727779 ++ List.replicate 1 101928764812 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 4 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 4 60424485067 ++ List.replicate 5 59724425029 ++ List.replicate 6 59033177370 ++ List.replicate 8 58350622743 ++ List.replicate 19 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 325575927980818376149550

-- Frozen witness row: a-27_50-11_20-m1k1
def row24 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 154172522044 ++ List.replicate 1 139453712567 ++ List.replicate 1 125900464449 ++ List.replicate 1 115834794727 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 93394146827 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 3 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 2 59724425029 ++ List.replicate 4 59033177370 ++ List.replicate 3 58350622743 ++ List.replicate 41 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 121764875649477217452646

-- Frozen witness row: a-27_50-11_20-m2k1
def row25 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 154172522044 ++ List.replicate 1 136652881772 ++ List.replicate 1 123321427417 ++ List.replicate 1 111045671764 ++ List.replicate 1 101928764812 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 2 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 2 59724425029 ++ List.replicate 3 59033177370 ++ List.replicate 4 58350622743 ++ List.replicate 46 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 198333993306142259143889

-- Frozen witness row: a-27_50-11_20-m2k2
def row26 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 154172522044 ++ List.replicate 1 136652881772 ++ List.replicate 1 123321427417 ++ List.replicate 1 111045671764 ++ List.replicate 1 101928764812 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 2 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 2 59724425029 ++ List.replicate 3 59033177370 ++ List.replicate 4 58350622743 ++ List.replicate 46 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 246944879260965845739209

-- Frozen witness row: a-29_50-59_100-m1k1
def row27 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 154172522044 ++ List.replicate 1 136652881772 ++ List.replicate 1 123321427417 ++ List.replicate 1 111045671764 ++ List.replicate 1 104151894752 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 1 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 1 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 2 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 2 59724425029 ++ List.replicate 2 59033177370 ++ List.replicate 3 58350622743 ++ List.replicate 49 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 107505325335898987423004

-- Frozen witness row: a-29_50-59_100-m2k1
def row28 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 151130823516 ++ List.replicate 1 133897885510 ++ List.replicate 1 118289277573 ++ List.replicate 1 108709727779 ++ List.replicate 1 99742015550 ++ List.replicate 1 91347063351 ++ List.replicate 1 86191218545 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 1 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 1 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 1 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 2 59724425029 ++ List.replicate 3 59033177370 ++ List.replicate 2 58350622743 ++ List.replicate 54 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 167161151425190361277229

-- Frozen witness row: a-29_50-59_100-m2k2
def row29 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 151130823516 ++ List.replicate 1 133897885510 ++ List.replicate 1 118289277573 ++ List.replicate 1 108709727779 ++ List.replicate 1 99742015550 ++ List.replicate 1 91347063351 ++ List.replicate 1 86191218545 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 1 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 1 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 1 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 2 59724425029 ++ List.replicate 3 59033177370 ++ List.replicate 2 58350622743 ++ List.replicate 54 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 217780949482932127569248

-- Frozen witness row: a-2_5-81_200-m1k1
def row30 : Row where
  rCaps := List.replicate 9 160408574090 ++ List.replicate 1 148138901231 ++ List.replicate 1 136652881772 ++ List.replicate 1 125900464449 ++ List.replicate 1 115834794727 ++ List.replicate 1 108709727779 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 93394146827 ++ List.replicate 1 89333479619 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 82153309123 ++ List.replicate 1 81176175902 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 2 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 2 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 2 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 3 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 3 66357101294 ++ List.replicate 4 65582037928 ++ List.replicate 4 64816804577 ++ List.replicate 4 64061267691 ++ List.replicate 5 63315295587 ++ List.replicate 6 62578758415 ++ List.replicate 7 61851528143 ++ List.replicate 8 61133478523 ++ List.replicate 10 60424485067 ++ List.replicate 2 59724425029
  tCaps := List.replicate 100 66553314396
  rTail := 59724425029
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 201254941449574598373991

-- Frozen witness row: a-2_5-81_200-m2k1
def row31 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 148138901231 ++ List.replicate 1 133897885510 ++ List.replicate 1 123321427417 ++ List.replicate 1 113420478561 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 95475287379 ++ List.replicate 1 91347063351 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 2 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 3 67142130115 ++ List.replicate 3 66357101294 ++ List.replicate 3 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 4 64061267691 ++ List.replicate 5 63315295587 ++ List.replicate 5 62578758415 ++ List.replicate 7 61851528143 ++ List.replicate 7 61133478523 ++ List.replicate 9 60424485067 ++ List.replicate 11 59724425029
  tCaps := List.replicate 100 66553314396
  rTail := 59724425029
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 388532553406251795782523

-- Frozen witness row: a-2_5-81_200-m2k2
def row32 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 148138901231 ++ List.replicate 1 133897885510 ++ List.replicate 1 123321427417 ++ List.replicate 1 113420478561 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 95475287379 ++ List.replicate 1 91347063351 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 2 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 3 67142130115 ++ List.replicate 3 66357101294 ++ List.replicate 3 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 4 64061267691 ++ List.replicate 5 63315295587 ++ List.replicate 5 62578758415 ++ List.replicate 7 61851528143 ++ List.replicate 7 61133478523 ++ List.replicate 9 60424485067 ++ List.replicate 11 59724425029
  tCaps := List.replicate 100 66553314396
  rTail := 59724425029
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 409272780052221617419013

-- Frozen witness row: a-41_100-21_50-m1k1
def row33 : Row where
  rCaps := List.replicate 9 160408574090 ++ List.replicate 1 148138901231 ++ List.replicate 1 136652881772 ++ List.replicate 1 125900464449 ++ List.replicate 1 115834794727 ++ List.replicate 1 108709727779 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 93394146827 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 2 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 2 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 3 67142130115 ++ List.replicate 3 66357101294 ++ List.replicate 3 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 4 64061267691 ++ List.replicate 5 63315295587 ++ List.replicate 5 62578758415 ++ List.replicate 6 61851528143 ++ List.replicate 8 61133478523 ++ List.replicate 8 60424485067 ++ List.replicate 9 59724425029
  tCaps := List.replicate 100 66553314396
  rTail := 59724425029
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 193555795815802029665646

-- Frozen witness row: a-41_100-21_50-m2k1
def row34 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 148138901231 ++ List.replicate 1 133897885510 ++ List.replicate 1 123321427417 ++ List.replicate 1 113420478561 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 2 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 2 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 3 66357101294 ++ List.replicate 3 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 4 64061267691 ++ List.replicate 4 63315295587 ++ List.replicate 5 62578758415 ++ List.replicate 6 61851528143 ++ List.replicate 6 61133478523 ++ List.replicate 8 60424485067 ++ List.replicate 10 59724425029 ++ List.replicate 7 59033177370
  tCaps := List.replicate 100 66553314396
  rTail := 59033177370
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 369127821992108830467161

-- Frozen witness row: a-41_100-21_50-m2k2
def row35 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 148138901231 ++ List.replicate 1 133897885510 ++ List.replicate 1 123321427417 ++ List.replicate 1 113420478561 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 2 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 2 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 3 66357101294 ++ List.replicate 3 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 4 64061267691 ++ List.replicate 4 63315295587 ++ List.replicate 5 62578758415 ++ List.replicate 6 61851528143 ++ List.replicate 6 61133478523 ++ List.replicate 8 60424485067 ++ List.replicate 10 59724425029 ++ List.replicate 7 59033177370
  tCaps := List.replicate 100 66553314396
  rTail := 59033177370
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 393553910122557096174521

-- Frozen witness row: a-43_100-11_25-m1k1
def row36 : Row where
  rCaps := List.replicate 9 160408574090 ++ List.replicate 1 148138901231 ++ List.replicate 1 133897885510 ++ List.replicate 1 123321427417 ++ List.replicate 1 115834794727 ++ List.replicate 1 108709727779 ++ List.replicate 1 101928764812 ++ List.replicate 1 95475287379 ++ List.replicate 1 91347063351 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 2 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 3 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 4 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 5 62578758415 ++ List.replicate 5 61851528143 ++ List.replicate 6 61133478523 ++ List.replicate 6 60424485067 ++ List.replicate 8 59724425029 ++ List.replicate 10 59033177370 ++ List.replicate 2 58350622743
  tCaps := List.replicate 100 66553314396
  rTail := 58350622743
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 179194467545061595182287

-- Frozen witness row: a-43_100-11_25-m2k1
def row37 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 145195940618 ++ List.replicate 1 131187973717 ++ List.replicate 1 120784595348 ++ List.replicate 1 111045671764 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 93394146827 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 2 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 3 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 3 64061267691 ++ List.replicate 4 63315295587 ++ List.replicate 4 62578758415 ++ List.replicate 5 61851528143 ++ List.replicate 5 61133478523 ++ List.replicate 6 60424485067 ++ List.replicate 7 59724425029 ++ List.replicate 9 59033177370 ++ List.replicate 11 58350622743
  tCaps := List.replicate 100 66553314396
  rTail := 58350622743
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 333490602947582076934824

-- Frozen witness row: a-43_100-11_25-m2k2
def row38 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 145195940618 ++ List.replicate 1 131187973717 ++ List.replicate 1 120784595348 ++ List.replicate 1 111045671764 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 93394146827 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 2 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 3 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 3 64061267691 ++ List.replicate 4 63315295587 ++ List.replicate 4 62578758415 ++ List.replicate 5 61851528143 ++ List.replicate 5 61133478523 ++ List.replicate 6 60424485067 ++ List.replicate 7 59724425029 ++ List.replicate 9 59033177370 ++ List.replicate 11 58350622743
  tCaps := List.replicate 100 66553314396
  rTail := 58350622743
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 364254972114954088609549

-- Frozen witness row: a-47_100-12_25-m1k1
def row39 : Row where
  rCaps := List.replicate 9 160408574090 ++ List.replicate 1 145195940618 ++ List.replicate 1 131187973717 ++ List.replicate 1 120784595348 ++ List.replicate 1 111045671764 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 93394146827 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 4 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 4 60424485067 ++ List.replicate 5 59724425029 ++ List.replicate 6 59033177370 ++ List.replicate 7 58350622743 ++ List.replicate 17 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 154556405595200481740381

-- Frozen witness row: a-47_100-12_25-m2k1
def row40 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 142301140439 ++ List.replicate 1 128522408602 ++ List.replicate 1 118289277573 ++ List.replicate 1 108709727779 ++ List.replicate 1 101928764812 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 3 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 3 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 4 60424485067 ++ List.replicate 5 59724425029 ++ List.replicate 5 59033177370 ++ List.replicate 7 58350622743 ++ List.replicate 24 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 273901650279743998514266

-- Frozen witness row: a-47_100-12_25-m2k2
def row41 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 142301140439 ++ List.replicate 1 128522408602 ++ List.replicate 1 118289277573 ++ List.replicate 1 108709727779 ++ List.replicate 1 101928764812 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 3 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 3 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 4 60424485067 ++ List.replicate 5 59724425029 ++ List.replicate 5 59033177370 ++ List.replicate 7 58350622743 ++ List.replicate 24 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 313949773861173335271380

-- Frozen witness row: a-49_100-1_2-m1k1
def row42 : Row where
  rCaps := List.replicate 9 160408574090 ++ List.replicate 1 142301140439 ++ List.replicate 1 128522408602 ++ List.replicate 1 118289277573 ++ List.replicate 1 111045671764 ++ List.replicate 1 101928764812 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 3 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 4 60424485067 ++ List.replicate 4 59724425029 ++ List.replicate 5 59033177370 ++ List.replicate 6 58350622743 ++ List.replicate 25 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 143991648137130120327973

-- Frozen witness row: a-49_100-1_2-m2k1
def row43 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 157264824936 ++ List.replicate 1 139453712567 ++ List.replicate 1 125900464449 ++ List.replicate 1 115834794727 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 93394146827 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 4 59724425029 ++ List.replicate 5 59033177370 ++ List.replicate 5 58350622743 ++ List.replicate 32 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 249043193421029060816904

-- Frozen witness row: a-49_100-1_2-m2k2
def row44 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 157264824936 ++ List.replicate 1 139453712567 ++ List.replicate 1 125900464449 ++ List.replicate 1 115834794727 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 93394146827 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 4 59724425029 ++ List.replicate 5 59033177370 ++ List.replicate 5 58350622743 ++ List.replicate 32 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 292367387273093159587762

-- Frozen witness row: a-51_100-13_25-m1k1
def row45 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 157264824936 ++ List.replicate 1 142301140439 ++ List.replicate 1 128522408602 ++ List.replicate 1 118289277573 ++ List.replicate 1 108709727779 ++ List.replicate 1 101928764812 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 3 61851528143 ++ List.replicate 3 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 4 59724425029 ++ List.replicate 4 59033177370 ++ List.replicate 5 58350622743 ++ List.replicate 32 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 134438072406896416618824

-- Frozen witness row: a-51_100-13_25-m2k1
def row46 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 157264824936 ++ List.replicate 1 139453712567 ++ List.replicate 1 125900464449 ++ List.replicate 1 113420478561 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 3 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 4 59033177370 ++ List.replicate 4 58350622743 ++ List.replicate 39 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 226958217726603435282813

-- Frozen witness row: a-51_100-13_25-m2k2
def row47 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 157264824936 ++ List.replicate 1 139453712567 ++ List.replicate 1 125900464449 ++ List.replicate 1 113420478561 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 3 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 4 59033177370 ++ List.replicate 4 58350622743 ++ List.replicate 39 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 272846532818676692915462

-- Frozen witness row: a-53_100-27_50-m1k1
def row48 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 157264824936 ++ List.replicate 1 139453712567 ++ List.replicate 1 125900464449 ++ List.replicate 1 115834794727 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 93394146827 ++ List.replicate 1 89333479619 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 3 61851528143 ++ List.replicate 2 61133478523 ++ List.replicate 3 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 4 59033177370 ++ List.replicate 4 58350622743 ++ List.replicate 38 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 125786017206949083201633

-- Frozen witness row: a-53_100-27_50-m2k1
def row49 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 154172522044 ++ List.replicate 1 136652881772 ++ List.replicate 1 123321427417 ++ List.replicate 1 111045671764 ++ List.replicate 1 104151894752 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 3 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 3 59033177370 ++ List.replicate 4 58350622743 ++ List.replicate 44 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 207322042617265102250551

-- Frozen witness row: a-53_100-27_50-m2k2
def row50 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 154172522044 ++ List.replicate 1 136652881772 ++ List.replicate 1 123321427417 ++ List.replicate 1 111045671764 ++ List.replicate 1 104151894752 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 3 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 3 59033177370 ++ List.replicate 4 58350622743 ++ List.replicate 44 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 255162088099479499975549

-- Frozen witness row: a-57_100-29_50-m1k1
def row51 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 154172522044 ++ List.replicate 1 136652881772 ++ List.replicate 1 123321427417 ++ List.replicate 1 113420478561 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 86191218545 ++ List.replicate 1 84146030839 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 1 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 1 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 2 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 2 59724425029 ++ List.replicate 3 59033177370 ++ List.replicate 3 58350622743 ++ List.replicate 47 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 110817695652618563199952

-- Frozen witness row: a-57_100-29_50-m2k1
def row52 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 151130823516 ++ List.replicate 1 133897885510 ++ List.replicate 1 120784595348 ++ List.replicate 1 108709727779 ++ List.replicate 1 99742015550 ++ List.replicate 1 93394146827 ++ List.replicate 1 87352847421 ++ List.replicate 1 84146030839 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 1 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 1 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 1 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 2 59033177370 ++ List.replicate 3 58350622743 ++ List.replicate 52 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 174289737495215468408417

-- Frozen witness row: a-57_100-29_50-m2k2
def row53 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 151130823516 ++ List.replicate 1 133897885510 ++ List.replicate 1 120784595348 ++ List.replicate 1 108709727779 ++ List.replicate 1 99742015550 ++ List.replicate 1 93394146827 ++ List.replicate 1 87352847421 ++ List.replicate 1 84146030839 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 1 64816804577 ++ List.replicate 2 64061267691 ++ List.replicate 1 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 1 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 2 59033177370 ++ List.replicate 3 58350622743 ++ List.replicate 52 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 224558262369429396288007

-- Frozen witness row: a-59_100-3_5-m1k1
def row54 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 151130823516 ++ List.replicate 1 133897885510 ++ List.replicate 1 120784595348 ++ List.replicate 1 111045671764 ++ List.replicate 1 101928764812 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 1 63315295587 ++ List.replicate 2 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 1 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 3 59724425029 ++ List.replicate 2 59033177370 ++ List.replicate 3 58350622743 ++ List.replicate 50 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 104346910700395916800175

-- Frozen witness row: a-59_100-3_5-m2k1
def row55 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 151130823516 ++ List.replicate 1 131187973717 ++ List.replicate 1 118289277573 ++ List.replicate 1 106412010631 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 86191218545 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 1 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 1 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 1 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 2 59724425029 ++ List.replicate 2 59033177370 ++ List.replicate 3 58350622743 ++ List.replicate 55 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 160420120339970972685752

-- Frozen witness row: a-59_100-3_5-m2k2
def row56 : Row where
  rCaps := List.replicate 7 160408574090 ++ List.replicate 1 151130823516 ++ List.replicate 1 131187973717 ++ List.replicate 1 118289277573 ++ List.replicate 1 106412010631 ++ List.replicate 1 97591051610 ++ List.replicate 1 91347063351 ++ List.replicate 1 86191218545 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 1 66357101294 ++ List.replicate 1 65582037928 ++ List.replicate 1 64816804577 ++ List.replicate 1 64061267691 ++ List.replicate 2 63315295587 ++ List.replicate 1 62578758415 ++ List.replicate 2 61851528143 ++ List.replicate 1 61133478523 ++ List.replicate 2 60424485067 ++ List.replicate 2 59724425029 ++ List.replicate 2 59033177370 ++ List.replicate 3 58350622743 ++ List.replicate 55 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 211320600240286904568861

-- Frozen witness row: a-81_200-41_100-m1k1
def row57 : Row where
  rCaps := List.replicate 9 160408574090 ++ List.replicate 1 148138901231 ++ List.replicate 1 136652881772 ++ List.replicate 1 125900464449 ++ List.replicate 1 115834794727 ++ List.replicate 1 108709727779 ++ List.replicate 1 104151894752 ++ List.replicate 1 97591051610 ++ List.replicate 1 93394146827 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 82153309123 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 2 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 2 72069407443 ++ List.replicate 2 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 3 67937261752 ++ List.replicate 3 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 4 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 5 64061267691 ++ List.replicate 4 63315295587 ++ List.replicate 6 62578758415 ++ List.replicate 6 61851528143 ++ List.replicate 8 61133478523 ++ List.replicate 9 60424485067 ++ List.replicate 6 59724425029
  tCaps := List.replicate 100 66553314396
  rTail := 59724425029
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 197324878440269062777371

-- Frozen witness row: a-81_200-41_100-m2k1
def row58 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 145195940618 ++ List.replicate 1 133897885510 ++ List.replicate 1 123321427417 ++ List.replicate 1 113420478561 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 2 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 2 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 3 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 3 66357101294 ++ List.replicate 3 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 4 64061267691 ++ List.replicate 4 63315295587 ++ List.replicate 5 62578758415 ++ List.replicate 6 61851528143 ++ List.replicate 7 61133478523 ++ List.replicate 9 60424485067 ++ List.replicate 10 59724425029 ++ List.replicate 4 59033177370
  tCaps := List.replicate 100 66553314396
  rTail := 59033177370
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 378628849589188845240778

-- Frozen witness row: a-81_200-41_100-m2k2
def row59 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 145195940618 ++ List.replicate 1 133897885510 ++ List.replicate 1 123321427417 ++ List.replicate 1 113420478561 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 80211627636 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 2 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 2 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 2 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 1 68742635506 ++ List.replicate 3 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 3 66357101294 ++ List.replicate 3 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 4 64061267691 ++ List.replicate 4 63315295587 ++ List.replicate 5 62578758415 ++ List.replicate 6 61851528143 ++ List.replicate 7 61133478523 ++ List.replicate 9 60424485067 ++ List.replicate 10 59724425029 ++ List.replicate 4 59033177370
  tCaps := List.replicate 100 66553314396
  rTail := 59033177370
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 401279824679066502062695

-- Frozen witness row: a-9_20-23_50-m1k1
def row60 : Row where
  rCaps := List.replicate 9 160408574090 ++ List.replicate 1 145195940618 ++ List.replicate 1 131187973717 ++ List.replicate 1 120784595348 ++ List.replicate 1 113420478561 ++ List.replicate 1 106412010631 ++ List.replicate 1 99742015550 ++ List.replicate 1 95475287379 ++ List.replicate 1 89333479619 ++ List.replicate 1 86191218545 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 80211627636 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 76475879139 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 2 72069407443 ++ List.replicate 1 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 2 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 1 67937261752 ++ List.replicate 2 67142130115 ++ List.replicate 3 66357101294 ++ List.replicate 2 65582037928 ++ List.replicate 3 64816804577 ++ List.replicate 3 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 4 62578758415 ++ List.replicate 4 61851528143 ++ List.replicate 5 61133478523 ++ List.replicate 5 60424485067 ++ List.replicate 6 59724425029 ++ List.replicate 8 59033177370 ++ List.replicate 9 58350622743 ++ List.replicate 5 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 166245236468496996024097

-- Frozen witness row: a-9_20-23_50-m2k1
def row61 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 142301140439 ++ List.replicate 1 128522408602 ++ List.replicate 1 118289277573 ++ List.replicate 1 111045671764 ++ List.replicate 1 101928764812 ++ List.replicate 1 95475287379 ++ List.replicate 1 91347063351 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 2 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 3 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 3 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 4 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 5 60424485067 ++ List.replicate 6 59724425029 ++ List.replicate 7 59033177370 ++ List.replicate 8 58350622743 ++ List.replicate 14 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 301909141794953466927543

-- Frozen witness row: a-9_20-23_50-m2k2
def row62 : Row where
  rCaps := List.replicate 8 160408574090 ++ List.replicate 1 142301140439 ++ List.replicate 1 128522408602 ++ List.replicate 1 118289277573 ++ List.replicate 1 111045671764 ++ List.replicate 1 101928764812 ++ List.replicate 1 95475287379 ++ List.replicate 1 91347063351 ++ List.replicate 1 87352847421 ++ List.replicate 1 85161975756 ++ List.replicate 1 83143201783 ++ List.replicate 1 81176175902 ++ List.replicate 1 79259492282 ++ List.replicate 1 78319600203 ++ List.replicate 1 77391784131 ++ List.replicate 1 75571722602 ++ List.replicate 1 74679154172 ++ List.replicate 1 73798015738 ++ List.replicate 1 72928151402 ++ List.replicate 1 72069407443 ++ List.replicate 2 71221632287 ++ List.replicate 1 70384676481 ++ List.replicate 1 69558392657 ++ List.replicate 2 68742635506 ++ List.replicate 2 67937261752 ++ List.replicate 1 67142130115 ++ List.replicate 2 66357101294 ++ List.replicate 3 65582037928 ++ List.replicate 2 64816804577 ++ List.replicate 3 64061267691 ++ List.replicate 3 63315295587 ++ List.replicate 3 62578758415 ++ List.replicate 4 61851528143 ++ List.replicate 4 61133478523 ++ List.replicate 5 60424485067 ++ List.replicate 6 59724425029 ++ List.replicate 7 59033177370 ++ List.replicate 8 58350622743 ++ List.replicate 14 57676643464
  tCaps := List.replicate 100 66553314396
  rTail := 57676643464
  tTail := 66553314396
  rBudget := 455946922433
  tBudget := 6650837008243
  prefixLength := 100
  baseEnergy := 337818916375168944730014

-- Frozen witness row: scalar-aligned-351_500-H
def row63 : Row where
  rCaps := List.replicate 4 282817005055 ++ List.replicate 80 194121479255
  tCaps := List.replicate 4 94833755317 ++ List.replicate 80 91261859388
  rTail := 194121479255
  tTail := 91261859388
  rBudget := 640392369956
  tBudget := 7615728241235
  prefixLength := 84
  baseEnergy := 0

def row : Fin 64 → Row := ![row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19,row20,row21,row22,row23,row24,row25,row26,row27,row28,row29,row30,row31,row32,row33,row34,row35,row36,row37,row38,row39,row40,row41,row42,row43,row44,row45,row46,row47,row48,row49,row50,row51,row52,row53,row54,row55,row56,row57,row58,row59,row60,row61,row62,row63]

def rcap (k : Fin 64) (i : ℕ) : ℕ := (row k).rCaps.getD i (row k).rTail
def tcap (k : Fin 64) (i : ℕ) : ℕ := (row k).tCaps.getD i (row k).tTail

structure DistinguishedRow where
  exponential : ℕ
  firstCap : ℕ
  restCap : ℕ
  restMass : ℕ

-- Frozen witness row: scalar-distinguished-1_10
def distinguished0 : DistinguishedRow := ⟨718923733432,73197832907,49178471349,5218115615275⟩
-- Frozen witness row: scalar-distinguished-1_100
def distinguished1 : DistinguishedRow := ⟨967538559590,4744377657,2064932024,681394626876⟩
-- Frozen witness row: scalar-distinguished-3_10
def distinguished2 : DistinguishedRow := ⟨371576691023,129290047599,101292826904,7146916807239⟩

def distinguished : Fin 3 → DistinguishedRow := ![distinguished0, distinguished1, distinguished2]

end GoldbachActiveRoundedData


