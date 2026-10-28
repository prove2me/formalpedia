-- Prove2me | Definitions.Def_TaoFivePrimes_RH14To100ArithmeticCore
-- name    : TaoFivePrimes_RH14To100ArithmeticCore
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T09:45:40.887214+00:00
-- url     : https://prove2.me/theorems/47f15563-fccf-451b-a04e-3fbf07d78a5b
-- title:
--   RH height 14–100 — core arithmetic interface
-- statement:
--   The core arithmetic interface for the existing height-14–100 finite certificate. This module defines the proposed data structures and exact integer validators, without asserting numerical correctness or a Riemann-hypothesis conclusion. It extracts the ordinary definitions from sometik179’s publicly submitted certificate, with the theta/Mellin attribution to Gabewhigham retained.
--
--   **Port note.** This is a port, to the Mathlib `777aaa6` / Lean v4.29.0-rc3 environment of the Riemann Hypothesis mission tree, of the definition `TaoFivePrimes_RH14To100ArithmeticCore` (id `7504b59a-c9de-4c74-8e27-706c5f8bb31d`, env `0df444a`, published by @raresbuhai). The Lean source is unchanged.
-- source:
--   sometik179, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a (2026-10-03), https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a. Original theta/Mellin attribution: Gabewhigham. These definitions already occur in public pilot 9fe11bf7-b735-43df-b4a3-f64c598366d3 and the published finite arithmetic interface 9b37fd72-f28f-4143-ba7e-0c2e92b04787; only dependency partitioning is changed.; ported from 0df444a definition 7504b59a-c9de-4c74-8e27-706c5f8bb31d

/- Ordinary finite arithmetic definitions extracted from sometik179's
height-14–100 certificate, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a.
Theta/Mellin attribution to Gabewhigham is retained. No certificate assertion
or RH theorem is supplied in this definition interface. -/
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

section Height100Module0

open Finset
namespace CertifiedPackedConvolution

def encode (bits : ℕ) : List ℕ → ℕ
  | [] => 0
  | x::xs => x+Nat.shiftLeft (encode bits xs) bits

end CertifiedPackedConvolution

end Height100Module0

section Height100Module1

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedMomentConvolution

end CertifiedMomentConvolution

end Height100Module1

section Height100Module2

open Finset

namespace CertifiedTaylorQuadrature

end CertifiedTaylorQuadrature

end Height100Module2

section Height100Module3

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

end CertifiedMomentConvolution

end Height100Module3

section Height100Module4

open Finset
namespace CertifiedExponentialJets
open CertifiedTaylorQuadrature CertifiedMomentConvolution

end CertifiedExponentialJets

end Height100Module4

section Height100Module5

open Finset
namespace CertifiedIntegerExponentialJets
open CertifiedMomentConvolution CertifiedExponentialJets

end CertifiedIntegerExponentialJets

end Height100Module5

section Height100Module6

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace CertifiedSignedODEConvolution
open CertifiedIntegerExponentialJets

end CertifiedSignedODEConvolution

end Height100Module6

section Height100Module7

set_option autoImplicit false
namespace CertifiedListODEVectors
open CertifiedSignedODEConvolution
open Finset
open scoped BigOperators

def positiveList (f : List ℤ) : List ℕ := f.map Int.toNat
def negativeList (f : List ℤ) : List ℕ := f.map (fun x => (-x).toNat)

end CertifiedListODEVectors

end Height100Module7

section Height100Module8

set_option autoImplicit false
open Finset
namespace CertifiedPackedHorner
open CertifiedPackedConvolution

end CertifiedPackedHorner

namespace CertifiedPackedHorner

end CertifiedPackedHorner

end Height100Module8

section Height100Module9

namespace ZetaSix

end ZetaSix

end Height100Module9

section Height100Module10

namespace TaoZetaBounds

end TaoZetaBounds

end Height100Module10

section Height100Module11

namespace TaoZetaBounds

end TaoZetaBounds

end Height100Module11

section Height100Module12

open Finset

namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module12

section Height100Module13

open Finset

namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module13

section Height100Module14

namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module14

section Height100Module15

open Finset
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module15

section Height100Module16

open Finset
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module16

section Height100Module17

set_option autoImplicit false
set_option exponentiation.threshold 1024
set_option maxRecDepth 10000

namespace TaoZetaWide256

end TaoZetaWide256

end Height100Module17

section Height100Module18

open Finset
open scoped BigOperators
set_option autoImplicit false
set_option exponentiation.threshold 1024

namespace TaoZetaGlobal

end TaoZetaGlobal

end Height100Module18

section Height100Module19

set_option autoImplicit false

namespace TaoZetaCertificate

end TaoZetaCertificate

end Height100Module19

section Height100Module20

set_option autoImplicit false

namespace TaoZetaCertificate

end TaoZetaCertificate

end Height100Module20

section Height100Module21

set_option autoImplicit false

namespace TaoZetaCertificate

end TaoZetaCertificate

end Height100Module21

section Height100Module22

open Finset
namespace CertifiedComplexTaylor
open CertifiedTaylorQuadrature

end CertifiedComplexTaylor

end Height100Module22

section Height100Module23

set_option autoImplicit false

namespace TaoZetaWide

end TaoZetaWide

end Height100Module23

section Height100Module24

namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module24

section Height100Module25

open Finset
namespace CertifiedGlobalMoments
open CertifiedZetaQuadrature

end CertifiedGlobalMoments

end Height100Module25

section Height100Module26

open Finset
namespace CertifiedEvenPolynomial

end CertifiedEvenPolynomial

end Height100Module26

section Height100Module27

namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module27

section Height100Module28

namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module28

section Height100Module29

open Finset
namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module29

section Height100Module30

open Finset
namespace CertifiedLocalXi

end CertifiedLocalXi

end Height100Module30

section Height100Module31

open Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature

end CertifiedPolynomialTranslation

end Height100Module31

section Height100Module32

open Finset
namespace CertifiedPolynomialTranslation
open CertifiedTaylorQuadrature CertifiedGlobalMoments

end CertifiedPolynomialTranslation

end Height100Module32

section Height100Module33

set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

namespace CertifiedDenseGlobalPolynomial
open Finset CertifiedPolynomialTranslation

end CertifiedDenseGlobalPolynomial

end Height100Module33

section Height100Module34

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module34

section Height100Module35

set_option autoImplicit false
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module35

section Height100Module36

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open CertifiedFixedPoint

end CertifiedThetaPoints

end Height100Module36

section Height100Module37

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
open scoped BigOperators

namespace CertifiedHighPrecisionPi

end CertifiedHighPrecisionPi

end Height100Module37

section Height100Module38

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option Elab.async false

namespace CertifiedHighPrecisionPi

end CertifiedHighPrecisionPi

end Height100Module38

section Height100Module39

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module39

section Height100Module40

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace CertifiedThetaPoints
open CertifiedFixedPoint CertifiedHighPrecisionPi

end CertifiedThetaPoints

end Height100Module40

section Height100Module41

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open CertifiedFixedPoint

end CertifiedThetaPoints

end Height100Module41

section Height100Module42

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CertifiedThetaCandidates
open CertifiedThetaPoints CertifiedFixedPoint

end CertifiedThetaCandidates

end Height100Module42

section Height100Module43

namespace CertifiedStreamingODE
open CertifiedSignedODEConvolution

end CertifiedStreamingODE

end Height100Module43

section Height100Module44

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedJetRecords
open CertifiedThetaCandidates CertifiedThetaPoints CertifiedFixedPoint
open CertifiedListODEVectors CertifiedPackedConvolution CertifiedStreamingODE

end CertifiedJetRecords

end Height100Module44

section Height100Module45

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 20000

namespace CertifiedJetRecords
open CertifiedThetaPoints

end CertifiedJetRecords

end Height100Module45

section Height100Module46

end Height100Module46

section Height100Module47

namespace CertifiedJetRecords

end CertifiedJetRecords

end Height100Module47

section Height100Module48

set_option autoImplicit false
namespace CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedSignedODEConvolution
open CertifiedListODEVectors CertifiedStreamingODE CertifiedIntegerExponentialJets

end CertifiedJetRecords

end Height100Module48

section Height100Module49

set_option autoImplicit false
namespace CertifiedFixedPoint

end CertifiedFixedPoint

end Height100Module49

section Height100Module50

namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module50

section Height100Module51

open Finset
namespace CertifiedZetaQuadrature
set_option exponentiation.threshold 512
open CertifiedTaylorQuadrature CertifiedMomentConvolution

end CertifiedZetaQuadrature

end Height100Module51

section Height100Module52

open Finset
namespace CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution CertifiedExponentialJets

end CertifiedZetaQuadrature

end Height100Module52

section Height100Module53

open Finset
namespace CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedIntegerExponentialJets
open CertifiedZetaQuadrature CertifiedMomentConvolution CertifiedTaylorQuadrature

end CertifiedJetRecords

end Height100Module53

section Height100Module54

open Finset
namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

end CertifiedMomentConvolution

end Height100Module54

section Height100Module55

open Finset
namespace CertifiedMomentConvolution
open CertifiedTaylorQuadrature

set_option exponentiation.threshold 512

end CertifiedMomentConvolution

end Height100Module55

section Height100Module56

open Finset
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module56

section Height100Module57

open Finset
namespace CertifiedZetaQuadrature

end CertifiedZetaQuadrature

end Height100Module57

section Height100Module58
namespace CertifiedZetaQuadrature
end CertifiedZetaQuadrature

end Height100Module58

section Height100Module59

open Finset
namespace CertifiedGlobalQuadrature
open CertifiedZetaQuadrature CertifiedTaylorQuadrature

end CertifiedGlobalQuadrature

end Height100Module59

section Height100Module60

open Finset
namespace CertifiedZetaQuadrature
open CertifiedMomentConvolution CertifiedTaylorQuadrature

end CertifiedZetaQuadrature

end Height100Module60

section Height100Module61

open Finset
namespace CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution
set_option exponentiation.threshold 1024

end CertifiedZetaQuadrature

end Height100Module61

section Height100Module62

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Finset
open scoped BigOperators

namespace CertifiedGlobalJetCenters
open CertifiedJetRecords CertifiedThetaPoints CertifiedFixedPoint
open CertifiedMomentConvolution CertifiedZetaQuadrature

end CertifiedGlobalJetCenters

end Height100Module62

section Height100Module63

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace CertifiedPackedCorrelation
open CertifiedSignedODEConvolution CertifiedListODEVectors CertifiedPackedConvolution

end CertifiedPackedCorrelation

end Height100Module63

section Height100Module64

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CertifiedMomentWeights
open CertifiedMomentConvolution

end CertifiedMomentWeights

end Height100Module64

section Height100Module65

namespace CertifiedExponentialIntegerSequence

def expSeq (a : Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | n+1, j, e => e :: expSeq a n (j+1) (e*a/(j+1))

end CertifiedExponentialIntegerSequence

end Height100Module65

section Height100Module66

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
open scoped BigOperators
namespace CertifiedMomentArithmetic
open CertifiedFixedPoint CertifiedExponentialIntegerSequence
open CertifiedMomentConvolution

end CertifiedMomentArithmetic

end Height100Module66

section Height100Module67

set_option autoImplicit false
namespace CertifiedPackedExtraction
open CertifiedSignedODEConvolution

/-- Extract signed coefficient differences at a fixed stride. The two packed
integers are consumed sequentially, avoiding repeated large-prefix evaluation. -/
def extract (bits step : ℕ) : ℕ → ℕ → ℕ → List ℤ
  | 0, _, _ => []
  | n+1, p, q =>
    (((p &&& (Nat.shiftLeft 1 bits-1):ℕ):ℤ)-((q &&& (Nat.shiftLeft 1 bits-1):ℕ):ℤ)) ::
      extract bits step n (p >>> (bits*step)) (q >>> (bits*step))

end CertifiedPackedExtraction

end Height100Module67

section Height100Module68

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedMomentRecords
open CertifiedGlobalJetCenters CertifiedThetaCandidates CertifiedThetaPoints
open CertifiedJetRecords CertifiedFixedPoint CertifiedPackedConvolution
open CertifiedMomentArithmetic CertifiedListODEVectors CertifiedPackedExtraction

end CertifiedMomentRecords

end Height100Module68

section Height100Module69

namespace CertifiedExponentialSequenceCheck
open CertifiedExponentialIntegerSequence

def checkSteps (a : ℕ) : ℕ → List ℕ → Bool
  | _,[] => true
  | j,x::xs =>
    (match xs with | [] => true | y::_ => decide ((j+1)*y=a*x)) &&
      checkSteps a (j+1) xs

end CertifiedExponentialSequenceCheck

end Height100Module69

section Height100Module70

namespace CertifiedPackedExponentialSequence
open CertifiedPackedConvolution CertifiedExponentialSequenceCheck

end CertifiedPackedExponentialSequence

end Height100Module70

section Height100Module71

namespace CertifiedChunkedExponentialSequence
open CertifiedPackedConvolution CertifiedPackedExponentialSequence

end CertifiedChunkedExponentialSequence

end Height100Module71

section Height100Module72

namespace CertifiedChunkedEncoding
open CertifiedPackedConvolution CertifiedPackedExponentialSequence
open CertifiedChunkedExponentialSequence

/-- Each equality is local to at most `block` literal coefficients. -/
def checkChunks (bits block : ℕ) : List ℕ → List ℕ → Bool
  | xs,[] => decide (xs=[])
  | xs,p::ps => decide (p=encode bits (xs.take block)) &&
      checkChunks bits block (xs.drop block) ps

end CertifiedChunkedEncoding

end Height100Module72

section Height100Module73

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedMomentSequenceCache
open CertifiedMomentRecords CertifiedMomentArithmetic CertifiedPackedConvolution
open CertifiedExponentialIntegerSequence CertifiedExponentialSequenceCheck
open CertifiedChunkedEncoding CertifiedListODEVectors CertifiedPackedExtraction

end CertifiedMomentSequenceCache

end Height100Module73

section Height100Module74

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option exponentiation.threshold 20000

namespace CertifiedMomentRecords

open CertifiedListODEVectors CertifiedPackedExtraction CertifiedMomentArithmetic

end CertifiedMomentRecords

end Height100Module74

section Height100Module75
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CertifiedMomentRecords

end CertifiedMomentRecords

end Height100Module75

section Height100Module76

end Height100Module76

section Height100Module77
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CertifiedLocalCandidates
@[noinline] def _root_.CertifiedLocalCandidates.row.«0» : (@_root_.List (@_root_.Int)) :=
  [(-406827080),(-867638483),613809818,(-157251858),18789495,(-658192),(-94375),11615,(-196),(-45),3,0,0,0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«1» : (@_root_.List (@_root_.Int)) :=
  [(-7998592969),(-403942844),2470306197,(-901711631),144706680,(-9964369),(-217293),87740,(-4708),(-161),28,(-1),0,0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«2» : (@_root_.List (@_root_.Int)) :=
  [(-6699333329),2359811119,532214454,(-424077477),94352135,(-9702823),257049,47371,(-5034),72,18,(-1),0,0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«3» : (@_root_.List (@_root_.Int)) :=
  [(-4146436447),2482736455,(-266220479),(-137172071),51011860,(-7434535),457015,11486,(-3760),191,6,(-1),0,0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«4» : (@_root_.List (@_root_.Int)) :=
  [(-20230502795),17084482272,(-4390126517),18783413,208581792,(-46367165),4489602,(-113315),(-19320),1999,(-33),(-6),0,0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«5» : (@_root_.List (@_root_.Int)) :=
  [(-7350790074),8989078264,(-3481463553),474346060,39014687,(-22650063),3313932,(-201602),(-3641),1415,(-75),(-2),0,0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«6» : (@_root_.List (@_root_.Int)) :=
  [(-1349354651),3510452994,(-2005416986),463032527,(-31675411),(-7045102),1903437,(-189065),5612,646,(-73),2,0,0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«7» : (@_root_.List (@_root_.Int)) :=
  [5817139294,7369366121,(-8520645047),2976913903,(-445071376),7832926,7769472,(-1290100),84868,377,(-466),28,0,0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«8» : (@_root_.List (@_root_.Int)) :=
  [7212100000,(-2444039019),(-2090181888),1389926649,(-328618369),32053479,1062000,(-644168),71933,(-2753),(-168),24,(-1),0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«9» : (@_root_.List (@_root_.Int)) :=
  [3771727721,(-3606416838),432733842,398462715,(-170306177),28547425,(-1689262),(-180716),43136,(-3303),38,13,(-1),0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«10» : (@_root_.List (@_root_.Int)) :=
  [8529185943,(-20951332952),8637164970,(-352533354),(-566178453),166311236,(-20107938),535663,167980,(-24123),1213,27,(-7),0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«11» : (@_root_.List (@_root_.Int)) :=
  [(-4556809795),(-6283519616),5559127038,(-1330016254),(-8513617),63592981,(-13419833),1160614,6898,(-11804),1143,(-32),(-3),0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«12» : (@_root_.List (@_root_.Int)) :=
  [(-6568402280),1056161434,1976819510,(-956389946),147999204,6617375,(-5870666),915798,(-54177),(-2546),683,(-46),0,0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«13» : (@_root_.List (@_root_.Int)) :=
  [(-43422056550),27364509038,(-85899387),(-3867530223),1210943962,(-125782295),(-10681698),4579912,(-536250),19106,2311,(-337),15,0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«14» : (@_root_.List (@_root_.Int)) :=
  [(-18932432396),19768854702,(-5758937270),(-363114380),547355486,(-120878111),8311479,1156128,(-308187),27128,(-359),(-150),14,0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«15» : (@_root_.List (@_root_.Int)) :=
  [(-4849965916),8802403764,(-4631653842),809176037,89828640,(-60719684),9921910,(-414565),(-98312),18162,(-1183),(-13),8,(-1),0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«16» : (@_root_.List (@_root_.Int)) :=
  [1684950069,20783349199,(-21343802932),7410998604,(-842934321),(-134096058),55448494,(-6880882),130214,69923,(-9479),436,19,(-4),0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«17» : (@_root_.List (@_root_.Int)) :=
  [7607223284,(-3427372422),(-4816383078),3578543005,(-906432395),68022251,15024626,(-4306102),410145,1026,(-4303),441,(-13),(-1),0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«18» : (@_root_.List (@_root_.Int)) :=
  [2114726465,(-5546870793),1307166026,805422494,(-463591057),89947208,(-4261266),(-1370641),290964,(-21202),(-530),234,(-18),0,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«19» : (@_root_.List (@_root_.Int)) :=
  [(-16985621150),(-19539275697),17560283761,(-2681832688),(-1080932518),491792276,(-75092146),1935262,1063029,(-173935),9506,494,(-114),7,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«20» : (@_root_.List (@_root_.Int)) :=
  [(-22307843914),5241057053,6885322731,(-3475630664),373984571,122035612,(-44260555),5402680,(-40961),(-72019),9313,(-364),(-33),5,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«21» : (@_root_.List (@_root_.Int)) :=
  [(-13200036544),10462295235,(-631100088),(-1462745379),499229064,(-39281093),(-11873312),3461449,(-340651),(-3025),4343,(-451),11,2,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«22» : (@_root_.List (@_root_.Int)) :=
  [(-43803904385),65626461824,(-25316576220),61636212,2224179517,(-563909771),32813471,10112325,(-2394069),190466,4744,(-2364),199,(-2),(-1),0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«23» : (@_root_.List (@_root_.Int)) :=
  [(-1731388055),21505639757,(-16781208131),4211610635,107490010,(-264483175),52646233,(-2243628),(-763415),148443,(-9518),(-397),117,(-8),0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«24» : (@_root_.List (@_root_.Int)) :=
  [7097438869,(-19098008),(-5420165317),2939670388,(-540572115),(-22268827),25946860,(-4200925),126666,51652,(-8342),427,26,(-5),0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«25» : (@_root_.List (@_root_.Int)) :=
  [40569213484,(-41863756706),2387638910,9371042231,(-3959725893),569036659,28869255,(-21758593),2934627,(-57971),(-31632),4287,(-172),(-15),2,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«26» : (@_root_.List (@_root_.Int)) :=
  [7083408475,(-21925483190),12487767904,(-805320448),(-1250256187),436215411,(-50980340),(-2903533),1599176,(-182703),1970,1769,(-203),6,1,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«27» : (@_root_.List (@_root_.Int)) :=
  [(-4026131894),(-2500877305),6145116933,(-2490729190),154315741,137054384,(-40819583),3984409,244442,(-104927),10278,(-29),(-91),9,0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«28» : (@_root_.List (@_root_.Int)) :=
  [(-26179368231),34037899115,4442690625,(-11737738754),3727481901,(-212070883),(-128228186),33287026,(-2765185),(-179099),62334,(-5281),(-24),43,(-4),0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«29» : (@_root_.List (@_root_.Int)) :=
  [3981065397,21000109463,(-11832094984),(-511317850),1703984364,(-446530866),23003924,10499116,(-2409669),172730,11695,(-3390),250,3,(-2),0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«30» : (@_root_.List (@_root_.Int)) :=
  [13926490182,579126318,(-7102806787),2547325527,38406304,(-199624326),44656745,(-2078204),(-765730),157056,(-9818),(-692),170,(-11),0,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«31» : (@_root_.List (@_root_.Int)) :=
  [98308767355,(-65804302639),(-6166826209),14941591505,(-3986268785),(-10909220),196186627,(-38405484),1618941,504074,(-93209),5124,375,(-80),5,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«32» : (@_root_.List (@_root_.Int)) :=
  [37441868380,(-48387904418),16827110980,1589689329,(-2283118163),492951380,(-1962483),(-16625545),2903518,(-111441),(-30264),5084,(-247),(-19),3,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«33» : (@_root_.List (@_root_.Int)) :=
  [5664776094,(-16738508643),12524596977,(-3084028714),(-245298246),275104071,(-50661774),419345,1240166,(-196258),6902,1671,(-257),11,1,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«34» : (@_root_.List (@_root_.Int)) :=
  [(-16525486527),(-8398691935),38286876046,(-22587247234),4489383110,269843382,(-274819395),44730752,(-507860),(-827411),120197,(-3901),(-855),121,(-5),0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«35» : (@_root_.List (@_root_.Int)) :=
  [(-4696631514),18373907427,(-3061938299),(-5946410533),3165693760,(-544465383),(-22585532),23529889,(-3472780),47664,50005,(-6742),203,41,(-5),0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«36» : (@_root_.List (@_root_.Int)) :=
  [7287718199,4353518902,(-7289942885),1458016917,699441900,(-364631105),56518654,1453280,(-1767575),241165,(-3772),(-2766),349,(-10),(-2),0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«37» : (@_root_.List (@_root_.Int)) :=
  [62005612525,(-45404533787),(-15283629846),17111494491,(-3199529951),(-655650768),356889417,(-51158399),(-670618),1185189,(-151771),2617,1412,(-169),4,1]

@[noinline] def _root_.CertifiedLocalCandidates.row.«38» : (@_root_.List (@_root_.Int)) :=
  [14879860348,(-38926628278),14593465383,3148596284,(-2843020516),487013457,49928218,(-30357200),4097422,13368,(-71865),8745,(-163),(-67),8,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«39» : (@_root_.List (@_root_.Int)) :=
  [(-8637094855),(-9111580015),12075128599,(-3193943479),(-445355004),365951230,(-58016507),(-3053716),2281310,(-293983),1295,3981,(-465),9,3,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«40» : (@_root_.List (@_root_.Int)) :=
  [(-90059715981),51513637725,25998455647,(-24792891331),5312878230,462495909,(-385059613),57380482,1391185,(-1534081),190957,(-1991),(-2031),230,(-5),(-1)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«41» : (@_root_.List (@_root_.Int)) :=
  [(-31892774670),50786362142,(-16456800773),(-4638048074),3800466057,(-712383357),(-35626146),34304115,(-4881014),(-30731),93262,(-11332),173,96,(-11),0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«42» : (@_root_.List (@_root_.Int)) :=
  [880669737,15586422200,(-14640171218),3661568891,575247391,(-464456100),79896426,1868598,(-2651435),365597,(-2178),(-5169),619,(-12),(-4),0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«43» : (@_root_.List (@_root_.Int)) :=
  [56787533453,(-22560382675),(-36722755970),28625740463,(-6245895993),(-507208505),471425900,(-76900547),(-305758),1809635,(-245205),3637,2629,(-314),7,2]

@[noinline] def _root_.CertifiedLocalCandidates.row.«44» : (@_root_.List (@_root_.Int)) :=
  [19772820759,(-35346591952),12109382717,5413624609,(-4244664876),858912656,28676887,(-40846776),6474673,(-67416),(-110490),14912,(-322),(-123),15,0]

@[noinline] def _root_.CertifiedLocalCandidates.row.«45» : (@_root_.List (@_root_.Int)) :=
  [(-1442374727),(-7634670512),11218447299,(-3485988153),(-523367856),505939619,(-98402956),(-232917),3079674,(-483997),10304,6093,(-830),22,5,(-1)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«46» : (@_root_.List (@_root_.Int)) :=
  [(-14580389333),42088800169,12682894461,(-23624013580),6805114470,269004325,(-501952149),96229965,(-1773127),(-2048058),325063,(-9659),(-3056),427,(-13),(-2)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«47» : (@_root_.List (@_root_.Int)) :=
  [23232179902,22780420221,(-20286320058),(-618980812),3670580677,(-1003679673),11633460,42389901,(-8185931),269368,121255,(-19806),722,140,(-20),1]

@[noinline] def _root_.CertifiedLocalCandidates.row.«48» : (@_root_.List (@_root_.Int)) :=
  [27820409345,(-9680766174),(-9306970266),5318549971,(-209378570),(-446043614),118946661,(-4638528),(-3091525),614939,(-26720),(-6426),1104,(-46),(-6),1]

@[noinline] def _root_.CertifiedLocalCandidates.row.«49» : (@_root_.List (@_root_.Int)) :=
  [136076001450,(-147451019390),25528509576,21116748386,(-9638930482),656870413,439158368,(-117801966),6545519,1962965,(-412930),21284,3053,(-566),26,2]

@[noinline] def _root_.CertifiedLocalCandidates.row.«50» : (@_root_.List (@_root_.Int)) :=
  [26617655708,(-66438623170),41964100149,(-5724252382),(-3263308184),1339384188,(-112236637),(-35751209),10014338,(-668491),(-108660),25030,(-1455),(-129),27,(-1)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«51» : (@_root_.List (@_root_.Int)) :=
  [(-5643770879),(-6889901870),16423729750,(-8384275842),1100198114,374673978,(-150994934),14226636,2422418,(-744791),56011,5198,(-1380),88,5,(-1)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«52» : (@_root_.List (@_root_.Int)) :=
  [(-31543774988),62857874467,(-3035962485),(-26783152574),12951626525,(-1751815475),(-330943440),142980676,(-14645045),(-1348727),491372,(-40468),(-2087),697,(-48),(-2)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«53» : (@_root_.List (@_root_.Int)) :=
  [12491288399,18374277586,(-25594190519),5009247634,3126877754,(-1620669838),230177214,22248745,(-11634514),1278939,58205,(-29049),2590,64,(-32),2]

@[noinline] def _root_.CertifiedLocalCandidates.row.«54» : (@_root_.List (@_root_.Int)) :=
  [12028933181,(-11926665878),(-4370527444),6150977596,(-1394441393),(-259446534),168802885,(-25321806),(-1015278),826100,(-97265),(-1493),1550,(-149),(-1),1]

@[noinline] def _root_.CertifiedLocalCandidates.row.«55» : (@_root_.List (@_root_.Int)) :=
  [3720240708,(-82558812951),51185204146,4694582265,(-10331322286),2446822623,125784395,(-148931660),23761710,94549,(-516941),65569,(-359),(-749),78,(-1)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«56» : (@_root_.List (@_root_.Int)) :=
  [(-30843028907),4702834337,27157444896,(-13572282559),164624473,1315460372,(-323121800),2859499,11252185,(-1934822),39361,28657,(-3968),82,33,(-4)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«57» : (@_root_.List (@_root_.Int)) :=
  [(-11385828164),23691228676,(-3955327644),(-5645324598),2554892314,(-156709671),(-132508664),34491533,(-1444215),(-731145),138655,(-5236),(-1407),218,(-7),(-1)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«58» : (@_root_.List (@_root_.Int)) :=
  [50028706427,77101899999,(-84532364246),14374103829,8245385659,(-3687693919),328232551,107555369,(-30929996),1945628,406633,(-88434),4523,607,(-109),5]

@[noinline] def _root_.CertifiedLocalCandidates.row.«59» : (@_root_.List (@_root_.Int)) :=
  [61937164526,(-31801936116),(-22414753163),19274484847,(-3366327852),(-880790781),427969024,(-45945694),(-6985536),2385826,(-186768),(-18928),5063,(-315),(-22),5]

@[noinline] def _root_.CertifiedLocalCandidates.row.«60» : (@_root_.List (@_root_.Int)) :=
  [23125064115,(-34467490262),11738659347,3737248413,(-3190422340),579350085,67289526,(-41178330),5020493,342292,(-160719),14663,687,(-262),19,1]

@[noinline] def _root_.CertifiedLocalCandidates.row.«61» : (@_root_.List (@_root_.Int)) :=
  [15537377288,(-94860726290),98924664622,(-30332745759),(-3597471889),4091379453,(-783649935),(-29773752),33501159,(-4552608),(-93986),95424,(-9910),(-140),123,(-10)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«62» : (@_root_.List (@_root_.Int)) :=
  [(-11022006210),13374085936,15649895301,(-19027986766),5840903212,79253892,(-421184925),86818583,(-740191),(-2329957),354007,(-3385),(-5013),592,(-5),(-5)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«63» : (@_root_.List (@_root_.Int)) :=
  [4557055067,9406978181,(-10179835674),(-453065155),2683816722,(-875275892),39228890,35384200,(-8098665),314580,138804,(-24087),738,232,(-32),1]

@[noinline] def _root_.CertifiedLocalCandidates.row.«64» : (@_root_.List (@_root_.Int)) :=
  [52066179111,(-55307620316),(-30678404643),31382669607,(-3712506282),(-2860489677),1055916275,(-84912960),(-24195457),6484111,(-392710),(-70041),14532,(-679),(-94),15]

@[noinline] def _root_.CertifiedLocalCandidates.row.«65» : (@_root_.List (@_root_.Int)) :=
  [(-8157329208),(-46067527104),26180571844,5208132756,(-6123796933),1033057443,225942528,(-105173706),11060932,1297723,(-451457),35187,2876,(-784),47,3]

@[noinline] def _root_.CertifiedLocalCandidates.row.«66» : (@_root_.List (@_root_.Int)) :=
  [(-27794177854),3303618028,16911430093,(-7438231019),(-394954023),866849215,(-168643645),(-11423723),8799564,(-1105921),(-46748),27554,(-2584),(-83),38,(-3)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«67» : (@_root_.List (@_root_.Int)) :=
  [(-147178611116),165346344383,(-16682352679),(-37240231095),14844016856,(-326181479),(-946371970),205652454,(-15021),(-6241372),914977,297,(-14783),1635,3,(-17)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«68» : (@_root_.List (@_root_.Int)) :=
  [(-21983088924),73720145328,(-52662406737),6726357637,5613979318,(-2251895260),149866277,81756637,(-20256171),781373,374997,(-64888),1738,694,(-91),2]

@[noinline] def _root_.CertifiedLocalCandidates.row.«69» : (@_root_.List (@_root_.Int)) :=
  [9375551930,1090387683,(-17879103534),11488261758,(-1796894603),(-605085197),271932203,(-26305260),(-5558214),1672784,(-107861),(-18748),4022,(-187),(-28),5]

@[noinline] def _root_.CertifiedLocalCandidates.row.«70» : (@_root_.List (@_root_.Int)) :=
  [19147367511,(-89992321044),31789888335,25818315269,(-18693286500),3406669843,446989330,(-268859519),32421564,2783907,(-1181758),100395,7335,(-2204),139,9]

@[noinline] def _root_.CertifiedLocalCandidates.row.«71» : (@_root_.List (@_root_.Int)) :=
  [(-28311107388),(-5623700135),33171296304,(-13433181684),(-1957734067),2360786213,(-491717401),(-15404032),22110553,(-3170220),(-71000),72121,(-7514),(-173),107,(-8)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«72» : (@_root_.List (@_root_.Int)) :=
  [(-14281828323),21482554326,(-2460798018),(-7056139860),3084728420,(-64816378),(-235299298),56697378,(-1391617),(-1518458),258671,(-4066),(-3804),479,(-4),(-5)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«73» : (@_root_.List (@_root_.Int)) :=
  [5224394449,63701597584,(-81902830152),17372179744,9782561709,(-4943319099),447862314,183713743,(-53894458),3250952,859382,(-180853),7581,1712,(-268),8]

@[noinline] def _root_.CertifiedLocalCandidates.row.«74» : (@_root_.List (@_root_.Int)) :=
  [9816204349,(-29995885103),(-11310863122),19786802593,(-5023599653),(-865915256),603998361,(-78874592),(-10585240),4307585,(-374633),(-38008),10995,(-687),(-63),13]

@[noinline] def _root_.CertifiedLocalCandidates.row.«75» : (@_root_.List (@_root_.Int)) :=
  [(-17074812459),(-14659266186),16492808267,72649521,(-3338332757),947458079,29946074,(-58591817),9498679,330700,(-292439),32401,1053,(-585),48,2]

@[noinline] def _root_.CertifiedLocalCandidates.row.«76» : (@_root_.List (@_root_.Int)) :=
  [(-175785714198),97741954758,56406228807,(-47278523100),4534430724,4117544286,(-1327815411),49005904,45765600,(-9006050),147234,168582,(-23129),141,272,(-28)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«77» : (@_root_.List (@_root_.Int)) :=
  [(-61505835606),100108561046,(-34963797519),(-10959570756),9064395800,(-1294798543),(-371489331),146896564,(-11470994),(-2838595),708132,(-34595),(-8113),1416,(-45),(-11)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«78» : (@_root_.List (@_root_.Int)) :=
  [210718852,25774489930,(-29285476707),9258669511,1133040255,(-1281199868),224634888,22292388,(-13243447),1437276,129401,(-47294),3481,308,(-76),4]

@[noinline] def _root_.CertifiedLocalCandidates.row.«79» : (@_root_.List (@_root_.Int)) :=
  [60454489028,(-54826307617),(-40011672274),56394142523,(-18557061335),(-120127349),1394599380,(-289383989),(-3678886),9869386,(-1351996),(-27980),27080,(-2612),(-72),36]

@[noinline] def _root_.CertifiedLocalCandidates.row.«80» : (@_root_.List (@_root_.Int)) :=
  [4443513320,(-34108342199),31660531441,(-810474917),(-7662770894),2872336075,(-181436106),(-118075042),29709432,(-1096476),(-606160),104054,(-1995),(-1324),162,(-1)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«81» : (@_root_.List (@_root_.Int)) :=
  [(-3876610632),8799602047,7545340876,(-8984252160),1691514291,722068390,(-351065480),38409752,7506211,(-2514604),178214,29694,(-6788),317,54,(-9)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«82» : (@_root_.List (@_root_.Int)) :=
  [55902001744,55158521431,(-63681416297),(-4404598838),16329434466,(-4204679685),(-377131263),344196720,(-50474432),(-2973798),1783033,(-176530),(-10216),3812,(-265),(-17)]

@[noinline] def _root_.CertifiedLocalCandidates.row.«83» : (@_root_.List (@_root_.Int)) :=
  [55014479869,(-41391926845),(-20844456473),20477812315,(-1898386687),(-2076584275),658295486,(-13470426),(-27136590),5052459,(-30063),(-106102),13608,77,(-185),17]

@[noinline] def _root_.CertifiedLocalCandidates.row.«84» : (@_root_.List (@_root_.Int)) :=
  [9903556186,(-35941317403),17440135645,3699467129,(-4175989497),661233774,185489020,(-76910285),5865728,1680006,(-411432),18651,5203,(-874),23,8]

@[noinline] def _root_.CertifiedLocalCandidates.row.«85» : (@_root_.List (@_root_.Int)) :=
  [(-82971781208),(-27276835123),114696670500,(-49500199085),(-2353273152),6072099677,(-1218985296),(-99826549),71061366,(-8144848),(-737553),280256,(-20938),(-1966),482,(-24)]

@[noinline] def _root_.CertifiedLocalCandidates.coefficientNumerators : (@_root_.List (@_root_.List (@_root_.Int))) :=
  [_root_.CertifiedLocalCandidates.row.«0»,
  _root_.CertifiedLocalCandidates.row.«1»,
  _root_.CertifiedLocalCandidates.row.«2»,
  _root_.CertifiedLocalCandidates.row.«3»,
  _root_.CertifiedLocalCandidates.row.«4»,
  _root_.CertifiedLocalCandidates.row.«5»,
  _root_.CertifiedLocalCandidates.row.«6»,
  _root_.CertifiedLocalCandidates.row.«7»,
  _root_.CertifiedLocalCandidates.row.«8»,
  _root_.CertifiedLocalCandidates.row.«9»,
  _root_.CertifiedLocalCandidates.row.«10»,
  _root_.CertifiedLocalCandidates.row.«11»,
  _root_.CertifiedLocalCandidates.row.«12»,
  _root_.CertifiedLocalCandidates.row.«13»,
  _root_.CertifiedLocalCandidates.row.«14»,
  _root_.CertifiedLocalCandidates.row.«15»,
  _root_.CertifiedLocalCandidates.row.«16»,
  _root_.CertifiedLocalCandidates.row.«17»,
  _root_.CertifiedLocalCandidates.row.«18»,
  _root_.CertifiedLocalCandidates.row.«19»,
  _root_.CertifiedLocalCandidates.row.«20»,
  _root_.CertifiedLocalCandidates.row.«21»,
  _root_.CertifiedLocalCandidates.row.«22»,
  _root_.CertifiedLocalCandidates.row.«23»,
  _root_.CertifiedLocalCandidates.row.«24»,
  _root_.CertifiedLocalCandidates.row.«25»,
  _root_.CertifiedLocalCandidates.row.«26»,
  _root_.CertifiedLocalCandidates.row.«27»,
  _root_.CertifiedLocalCandidates.row.«28»,
  _root_.CertifiedLocalCandidates.row.«29»,
  _root_.CertifiedLocalCandidates.row.«30»,
  _root_.CertifiedLocalCandidates.row.«31»,
  _root_.CertifiedLocalCandidates.row.«32»,
  _root_.CertifiedLocalCandidates.row.«33»,
  _root_.CertifiedLocalCandidates.row.«34»,
  _root_.CertifiedLocalCandidates.row.«35»,
  _root_.CertifiedLocalCandidates.row.«36»,
  _root_.CertifiedLocalCandidates.row.«37»,
  _root_.CertifiedLocalCandidates.row.«38»,
  _root_.CertifiedLocalCandidates.row.«39»,
  _root_.CertifiedLocalCandidates.row.«40»,
  _root_.CertifiedLocalCandidates.row.«41»,
  _root_.CertifiedLocalCandidates.row.«42»,
  _root_.CertifiedLocalCandidates.row.«43»,
  _root_.CertifiedLocalCandidates.row.«44»,
  _root_.CertifiedLocalCandidates.row.«45»,
  _root_.CertifiedLocalCandidates.row.«46»,
  _root_.CertifiedLocalCandidates.row.«47»,
  _root_.CertifiedLocalCandidates.row.«48»,
  _root_.CertifiedLocalCandidates.row.«49»,
  _root_.CertifiedLocalCandidates.row.«50»,
  _root_.CertifiedLocalCandidates.row.«51»,
  _root_.CertifiedLocalCandidates.row.«52»,
  _root_.CertifiedLocalCandidates.row.«53»,
  _root_.CertifiedLocalCandidates.row.«54»,
  _root_.CertifiedLocalCandidates.row.«55»,
  _root_.CertifiedLocalCandidates.row.«56»,
  _root_.CertifiedLocalCandidates.row.«57»,
  _root_.CertifiedLocalCandidates.row.«58»,
  _root_.CertifiedLocalCandidates.row.«59»,
  _root_.CertifiedLocalCandidates.row.«60»,
  _root_.CertifiedLocalCandidates.row.«61»,
  _root_.CertifiedLocalCandidates.row.«62»,
  _root_.CertifiedLocalCandidates.row.«63»,
  _root_.CertifiedLocalCandidates.row.«64»,
  _root_.CertifiedLocalCandidates.row.«65»,
  _root_.CertifiedLocalCandidates.row.«66»,
  _root_.CertifiedLocalCandidates.row.«67»,
  _root_.CertifiedLocalCandidates.row.«68»,
  _root_.CertifiedLocalCandidates.row.«69»,
  _root_.CertifiedLocalCandidates.row.«70»,
  _root_.CertifiedLocalCandidates.row.«71»,
  _root_.CertifiedLocalCandidates.row.«72»,
  _root_.CertifiedLocalCandidates.row.«73»,
  _root_.CertifiedLocalCandidates.row.«74»,
  _root_.CertifiedLocalCandidates.row.«75»,
  _root_.CertifiedLocalCandidates.row.«76»,
  _root_.CertifiedLocalCandidates.row.«77»,
  _root_.CertifiedLocalCandidates.row.«78»,
  _root_.CertifiedLocalCandidates.row.«79»,
  _root_.CertifiedLocalCandidates.row.«80»,
  _root_.CertifiedLocalCandidates.row.«81»,
  _root_.CertifiedLocalCandidates.row.«82»,
  _root_.CertifiedLocalCandidates.row.«83»,
  _root_.CertifiedLocalCandidates.row.«84»,
  _root_.CertifiedLocalCandidates.row.«85»]

end CertifiedLocalCandidates

end Height100Module77

section Height100Module78

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option exponentiation.threshold 20000

namespace CertifiedGlobalTranslation
open CertifiedMomentRecords CertifiedPackedHorner CertifiedSignedODEConvolution
open CertifiedPackedExtraction CertifiedListODEVectors

end CertifiedGlobalTranslation

end Height100Module78

section Height100Module79

open Finset
namespace CertifiedPolynomialTranslation

end CertifiedPolynomialTranslation

end Height100Module79

section Height100Module80

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option exponentiation.threshold 20000
namespace CertifiedTranslationConvolution
open CertifiedGlobalTranslation CertifiedPackedConvolution CertifiedListODEVectors
open CertifiedExponentialIntegerSequence CertifiedPackedExtraction

end CertifiedTranslationConvolution

end Height100Module80

section Height100Module81

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CertifiedPackedTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction CertifiedExponentialIntegerSequence

end CertifiedPackedTranslation

end Height100Module81

section Height100Module82

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedLiteralTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction CertifiedExponentialIntegerSequence

end CertifiedLiteralTranslation

end Height100Module82

section Height100Module83
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace CertifiedLiteralTranslation

end CertifiedLiteralTranslation

end Height100Module83

section Height100Module84

namespace CertifiedExponentialSequenceBound
open CertifiedExponentialSequenceCheck CertifiedPackedExponentialSequence
open CertifiedPackedConvolution
set_option maxRecDepth 100000
set_option exponentiation.threshold 8192

end CertifiedExponentialSequenceBound

end Height100Module84

section Height100Module85

set_option autoImplicit false
open Finset
namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature CertifiedPolynomialTranslation

end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature
end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature
end CertifiedPackedHorner

namespace CertifiedPackedHorner
open CertifiedTaylorQuadrature CertifiedPolynomialTranslation

end CertifiedPackedHorner

end Height100Module85

section Height100Module86

set_option autoImplicit false
open Finset
namespace CertifiedTranslationAlgebra
open CertifiedPolynomialTranslation CertifiedPackedHorner CertifiedListODEVectors
open CertifiedPackedCorrelation CertifiedPackedConvolution CertifiedSignedODEConvolution

end CertifiedTranslationAlgebra

namespace CertifiedTranslationAlgebra
open CertifiedPackedConvolution CertifiedSignedODEConvolution

end CertifiedTranslationAlgebra

end Height100Module86

section Height100Module87

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
namespace CertifiedMomentRecords
open CertifiedPackedCorrelation CertifiedMomentArithmetic CertifiedMomentConvolution
open CertifiedListODEVectors CertifiedPackedExtraction CertifiedSignedODEConvolution
open CertifiedGlobalJetCenters CertifiedFixedPoint CertifiedPackedConvolution

end CertifiedMomentRecords

end Height100Module87

section Height100Module88

set_option autoImplicit false
namespace CertifiedIntegerRounding

end CertifiedIntegerRounding

end Height100Module88

section Height100Module89

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Finset
open scoped BigOperators

namespace CertifiedGlobalMomentEnclosure
open CertifiedMomentRecords CertifiedMomentArithmetic CertifiedGlobalJetCenters
open CertifiedZetaQuadrature CertifiedIntegerRounding

end CertifiedGlobalMomentEnclosure

end Height100Module89

section Height100Module90

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Finset
namespace CertifiedGlobalTranslation
open CertifiedPackedHorner CertifiedListODEVectors CertifiedPackedExtraction
open CertifiedSignedODEConvolution CertifiedTaylorQuadrature CertifiedPolynomialTranslation

end CertifiedGlobalTranslation

end Height100Module90

section Height100Module91

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Finset
namespace CertifiedPackedTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedListODEVectors CertifiedPackedExtraction
open CertifiedSignedODEConvolution CertifiedTranslationAlgebra CertifiedPackedExponentialSequence

end CertifiedPackedTranslation

end Height100Module91

section Height100Module92

namespace CertifiedPackedTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation CertifiedPolynomialTranslation

end CertifiedPackedTranslation

end Height100Module92

section Height100Module93

set_option autoImplicit false
set_option exponentiation.threshold 8192
namespace CertifiedLiteralTranslation
open CertifiedTranslationConvolution CertifiedGlobalTranslation
open CertifiedPackedConvolution CertifiedPackedExtraction

end CertifiedLiteralTranslation

end Height100Module93

section Height100Module94

set_option autoImplicit false
set_option maxHeartbeats 0

namespace TaoZetaPoly

end TaoZetaPoly

end Height100Module94

section Height100Module95

namespace CertifiedLocalPolynomial
open Finset CertifiedLocalXi

end CertifiedLocalPolynomial

end Height100Module95

section Height100Module96

namespace CertifiedIntegerLocalPolynomial
open Finset

end CertifiedIntegerLocalPolynomial

end Height100Module96

section Height100Module97

open Finset
set_option autoImplicit false

namespace TaoZetaNumerics

end TaoZetaNumerics

end Height100Module97

section Height100Module98

open Finset
set_option autoImplicit false
set_option maxHeartbeats 0

namespace TaoZetaNumerics

end TaoZetaNumerics

end Height100Module98

section Height100Module99

namespace CertifiedLocalPolynomial
open Finset TaoZetaNumerics

end CertifiedLocalPolynomial

end Height100Module99

section Height100Module100

namespace CertifiedLocalPolynomial
open Finset CertifiedLocalXi

end CertifiedLocalPolynomial

end Height100Module100

section Height100Module101

open Finset
set_option autoImplicit false
set_option maxHeartbeats 0
namespace TaoZetaNumerics

end TaoZetaNumerics

end Height100Module101

section Height100Module102

namespace CertifiedLocalBoxes
open CertifiedLocalCandidates CertifiedLocalPolynomial TaoZetaNumerics
open Finset

end CertifiedLocalBoxes

end Height100Module102

section Height100Module103

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

end CertifiedFastLocalBoxes

end Height100Module103

section Height100Module104

namespace CertifiedStreamingBernstein
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

end CertifiedStreamingBernstein

end Height100Module104

section Height100Module105

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes CertifiedFastLocalBoxes CertifiedStreamingBernstein
open TaoZetaNumerics

end CertifiedStreamingLocalBoxes

end Height100Module105

section Height100Module106

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes
open CertifiedLocalPolynomial CertifiedIntegerLocalPolynomial TaoZetaNumerics Finset

end CertifiedFastLocalBoxes

end Height100Module106

section Height100Module107

namespace CertifiedLocalBoxes
open CertifiedLocalCandidates CertifiedLocalPolynomial CertifiedLocalXi

end CertifiedLocalBoxes

end Height100Module107

section Height100Module108

namespace CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedIntegerLocalPolynomial CertifiedLocalPolynomial CertifiedLocalXi

end CertifiedFastLocalBoxes

end Height100Module108

section Height100Module109

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes CertifiedFastLocalBoxes CertifiedStreamingBernstein

end CertifiedStreamingLocalBoxes

end Height100Module109

section Height100Module110

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace CertifiedStreamingLocalBoxes
open CertifiedLocalBoxes

end CertifiedStreamingLocalBoxes

end Height100Module110

section Height100Module111

namespace CertifiedStreamingLocalBoxes
open CertifiedFastLocalBoxes
open CertifiedLocalBoxes CertifiedLocalPolynomial CertifiedLocalXi

end CertifiedStreamingLocalBoxes

end Height100Module111

section Height100Module112

namespace CertifiedHeight100
open CertifiedPolynomialTranslation CertifiedGlobalMoments CertifiedLocalXi

end CertifiedHeight100

end Height100Module112

section Height100Module113

set_option autoImplicit false
namespace TaoFivePrimes

end TaoFivePrimes

end Height100Module113


def TaoFivePrimes_RH14To100ArithmeticCore : Nat := 14


