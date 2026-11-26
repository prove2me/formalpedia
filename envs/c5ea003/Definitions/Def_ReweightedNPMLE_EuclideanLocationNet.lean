-- Prove2me | Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
-- name    : ReweightedNPMLE_EuclideanLocationNet
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:17:07.637281+00:00
-- url     : https://prove2.me/theorems/04a63fc7-027f-41c4-984c-a69a3ba37326
-- title:
--   An internal Euclidean net constructed from coordinate cells
-- statement:
--   For a nonempty set \(K\subseteq\mathbb R^d\), a bound \(\|u\|\le S\) for \(u\in K\), and \(\varepsilon>0\), set
--   \[
--   h=\frac{\varepsilon}{d+2},\qquad
--   M=\left\lfloor\frac{2S}{h}\right\rfloor_{\mathbb N}+1.
--   \]
--   Assign \(u\in K\) the coordinate code \(c_i(u)=\lfloor(u_i+S)/h\rfloor_{\mathbb N}\in\{0,\ldots,M-1\}\). For each occupied code, choose a point of \(K\) with that code. For an empty code, use a fixed point of \(K\). The location net is the finite set of all these representatives, with repetitions removed. It is internal to \(K\), has at most \(M^d\) points, and the cell-width choice gives Euclidean approximation within \(\varepsilon\).
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/EuclideanLocationNet.lean#L18-L174

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian

/-!
# Explicit finite nets for bounded Euclidean sets

This module implements the coordinate-cell construction used in the paper's
entropy argument.  A set contained in the radius-`S` Euclidean ball is split
into cells of coordinate width `ε / (d + 2)`.  Choosing one point of the set
from each occupied cell gives an internal `ε`-net with an explicit cardinality
bound.
-/

open scoped BigOperators

namespace ReweightedNPMLE

/-- Coordinate width in the explicit bounded-set location net.  The harmless
`d + 2` denominator gives a strict Euclidean error smaller than `ε` in every
dimension, including dimension zero. -/
noncomputable def boundedLocationCellWidth (d : ℕ) (ε : ℝ) : ℝ :=
  ε / (d + 2)

/-- Number of coordinate cells needed on the interval `[-S,S]`. -/
noncomputable def boundedLocationCellCount (d : ℕ) (S ε : ℝ) : ℕ :=
  Nat.floor (2 * S / boundedLocationCellWidth d ε) + 1

theorem boundedLocationCellWidth_pos (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 < boundedLocationCellWidth d ε := by
  unfold boundedLocationCellWidth
  positivity

/-- Each coordinate of a Euclidean point is bounded by its Euclidean norm. -/
theorem abs_coord_le_norm {d : ℕ} (u : Point d) (i : Fin d) :
    |u i| ≤ ‖u‖ := by
  have hsq : (u i) ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (u j)) (Finset.mem_univ i)
  nlinarith [abs_nonneg (u i), norm_nonneg u, sq_abs (u i)]



theorem boundedLocation_scaled_coord_le {d : ℕ} {S ε : ℝ}
    (hε : 0 < ε) (u : Point d) (hu : ‖u‖ ≤ S) (i : Fin d) :
    (u i + S) / boundedLocationCellWidth d ε ≤
      2 * S / boundedLocationCellWidth d ε := by
  have hi := (abs_coord_le_norm u i).trans hu
  have hup : u i ≤ S := (le_abs_self (u i)).trans hi
  exact div_le_div_of_nonneg_right (by linarith)
    (boundedLocationCellWidth_pos d hε).le

/-- Coordinate-cell code of a point in a bounded set. -/
noncomputable def boundedLocationCellCode {d : ℕ} {K : Set (Point d)}
    (S ε : ℝ) (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (u : K) :
    Fin d → Fin (boundedLocationCellCount d S ε) := fun i =>
  ⟨Nat.floor (((u : Point d) i + S) / boundedLocationCellWidth d ε), by
    unfold boundedLocationCellCount
    exact Nat.lt_succ_of_le (Nat.floor_mono
      (boundedLocation_scaled_coord_le hε (u : Point d)
        (hKbound u u.property) i))⟩



/-- A representative in `K` for a cell.  Empty cells use an arbitrary point
of the nonempty set; duplicates are discarded when the finite net is formed. -/
noncomputable def boundedLocationRepresentative {d : ℕ} (K : Set (Point d))
    (hKnonempty : K.Nonempty) (S ε : ℝ) (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S)
    (c : Fin d → Fin (boundedLocationCellCount d S ε)) : K := by
  classical
  exact if h : ∃ u : K,
      boundedLocationCellCode S ε hε hKbound u = c then h.choose
    else ⟨hKnonempty.choose, hKnonempty.choose_spec⟩



/-- The explicit finite internal net of a nonempty bounded Euclidean set. -/
noncomputable def boundedLocationNet {d : ℕ} (K : Set (Point d))
    (hKnonempty : K.Nonempty) (S ε : ℝ) (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) : Finset (Point d) := by
  classical
  exact (Finset.univ : Finset
      (Fin d → Fin (boundedLocationCellCount d S ε))).image
    (fun c ↦ (boundedLocationRepresentative K hKnonempty S ε hε
      hKbound c : Point d))







end ReweightedNPMLE


