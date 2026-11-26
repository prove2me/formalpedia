-- Prove2me | Theorems.Thm_section5_phase_amplitude_norm
-- name    : section5_phase_amplitude_norm
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:23:45.698559+00:00
-- url     : https://prove2.me/theorems/e3437e20-6b10-51a4-ab10-d71b9d27b8d4
-- title:
--   Unit norm of the discrete threshold-phase amplitude
-- statement:
--   For $w\in\mathbb R^n$, let $f_w(x)=\operatorname{sgn}(\langle w,x\rangle)$, with the sign at zero equal to $1$. Let $n,q\ge0$, and let $g(z)$ be the grid point associated with $z\in\{0,1\}^{nq}$. Put $W(z)=e^{-\|g(z)\|^2/2}$ and $a(z)=\sqrt{W(z)/\sum_yW(y)}$. For every $w\in\mathbb R^n$, the finite complex vector with coordinates $f_w(g(z))a(z)$ has Euclidean norm one:
--
--   $$
--   \left(\sum_z|f_w(g(z))a(z)|^2\right)^{1/2}=1.
--   $$
--
--   This verifies normalization of the discrete Gaussian amplitude after threshold phase encoding.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5ExamplePhase.lean, section5_phase_amplitude_norm, lines 73–91.

import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_Section5Verified_Section5ExamplePhase
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

theorem section5_phase_amplitude_norm {n q : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    ‖(WithLp.toLp 2 (fun x : Qubits (n*q) =>
      (ltf w 0 (gridPoint x):ℂ)*section5_grid_amplitude x) :
      EuclideanSpace ℂ (Qubits (n*q)))‖ = 1 := by sorry
