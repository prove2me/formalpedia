-- Prove2me | Definitions.Def_mme_released_global_yz_expression_primitives
-- name    : mme_released_global_yz_expression_primitives
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-22T12:51:35.911575+00:00
-- url     : https://prove2.me/theorems/886295c2-0cc8-453f-b65b-8d6138ae3b3d
-- title:
--   Exact global Y/Z certificate: expression primitives
-- statement:
--   One component of the exact six-orientation Y/Z certificate: word enumeration and cached integer counts, finite entropy expressions, or outward-rounded logarithm intervals. All numerical data are connected to the published profile by the accompanying full proofs. Tables are split by orientation to fit publication and compilation limits.
-- source:
--   Exact released global candidate from primitive seed f8187420c24231b83d9d1fb7b327fee76cd50ada0af0525e77b3d3b0d8f4d4e6.

import Definitions.Def_mme_released_global_yz_word_data
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace MME.ReleasedGlobalYZ

def wordQ (o : Fin 6) (i : Fin 2) (s : Fin 45) (t : Fin 81) : ℚ :=
  (alpha o s * cachedCounts o i s t : ℕ) / (denominator : ℚ)^5

def boundary (i : Fin 2) (s : Fin 45) : Prop :=
  if i = 0 then shapeVector s 2 = 0 else shapeVector s 0 = 0 ∨ shapeVector s 1 = 0
instance (i : Fin 2) (s : Fin 45) : Decidable (boundary i s) := by unfold boundary; infer_instance

def gradeQ (o : Fin 6) (i : Fin 2) (j : Fin 9) (t : Fin 81) : ℚ :=
  ∑ s : Fin 45, if shapeVector s (RecursiveYZ.yzMode i) = j then wordQ o i s t else 0

def interiorQ (o : Fin 6) (i : Fin 2) (j : Fin 9) (t : Fin 81) : ℚ :=
  ∑ s : Fin 45, if ¬ boundary i s ∧ shapeVector s (RecursiveYZ.yzMode i) = j then wordQ o i s t else 0

abbrev Terms := List (ℚ × ℚ)
def massTerms (l : List ℚ) : Terms := l.map (fun q ↦ (-q,q)) ++ [(l.sum,l.sum)]
def negative (l : Terms) : Terms := l.map (fun p ↦ (-p.1,p.2))
def rawTerms (o : Fin 6) (i : Fin 2) : Terms :=
  massTerms (List.ofFn (ReleasedGlobalNumeric.marginalQ o (RecursiveYZ.yzMode i))) ++
  (List.ofFn (fun j : Fin 9 ↦ massTerms (List.ofFn (gradeQ o i j)))).flatten ++
  negative ((List.ofFn (fun s : Fin 45 ↦ if boundary i s then massTerms (List.ofFn (wordQ o i s)) else [])).flatten) ++
  negative ((List.ofFn (fun j : Fin 9 ↦ massTerms (List.ofFn (interiorQ o i j)))).flatten)

def prune (l : Terms) : Terms := l.filter (fun p ↦ p.1 != 0 && p.2 != 0 && p.2 != 1)
noncomputable def evaluate (l : Terms) : ℝ := (l.map (fun p ↦ (p.1 : ℝ)*Real.log (p.2 : ℝ))).sum

/-- Signed log term, scale, and outward rounded logarithm endpoints. -/
abbrev Entry := (ℚ × ℚ) × (ℕ × ℚ × ℚ)

end MME.ReleasedGlobalYZ


