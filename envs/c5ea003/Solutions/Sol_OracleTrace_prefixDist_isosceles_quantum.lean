-- Prove2me | solution 1 for OracleTrace.prefixDist_isosceles_quantum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T11:11:14.470381+00:00
-- url     : https://prove2.me/submissions/17f498e6-f319-4237-9006-29ae842eac8d

-- Sol generated from Bridges/OracleTraceUltrametricEntropy.lean
import Mathlib
import Definitions.Def_Bridges_LongestCommonValuedPrefix
import Definitions.Def_Bridges_OracleTraceUltrametricEntropy
import Theorems.Thm_OracleTrace_lcvpLen_ge_min_of_triangle
import Theorems.Thm_OracleTrace_lcvpLen_symmetric
/-
  # Oracle Trace Ultrametric Entropy

  A non-Archimedean metric geometry for oracle traces, connecting
  ultrametric valuation theory, thermodynamic entropy bounds,
  certified ML robustness, and post-quantum separation principles.

  Bridge: connects ultrametric valuation geometry to thermodynamic
  entropy bounds, certified_robustness in ML, and post_quantum_security.

  Keywords: ultrametric, entropy, capacity, certified_robustness,
            post_quantum_security, lattice_crypto, thermodynamic
-/
open List Finset OracleTrace

open OracleTrace

variable {α : Type*} [DecidableEq α]

/-! ## Section 1: Prefix Distance and Gap -/



/-! ## Section 2: Oracle Trace Model -/




/-! ## Section 3: Entropy and Capacity Proxies -/




/-! ## Section 4: Ultrametric Balls and Certified Robustness -/




/-! ## Section 5: Normalized Entropy Proxy -/


/-! ## Section 6: prefixGap Basic Properties -/








/-! ## Section 7: Monotonicity of Powers on (0,1) -/


/-! ## Section 8: The Strong Ultrametric Inequality -/


/-
**Isosceles strengthening**: if two pairwise distances differ,
the third equals the larger. Hallmark of non-Archimedean geometry.
Bridge: connects to quantum oracle semantics and certified_robustness.
-/

/-! ## Section 9: prefixDist Concatenation Contraction -/


/-! ## Section 10: Ball Properties -/



/-! ## Section 11: Entropy–Capacity Theorems -/


/-
**The entropy–capacity inequality**.
Bridge: connects thermodynamic oracle semantics to information_theory.
-/


/-! ## Section 12: Post-Quantum Separation -/


/-! ## Section 13: Certified Robustness Radius -/


/-! ## Section 14: Existence Theorems -/




/-! ## Section 15: prefixDist Basic Properties -/





/-! ## Section 16: Min-Length Characterization -/


/-! ## Section 17: Cross-Domain Theorems -/



/-
Ultrametric clustering trichotomy: in any triple, at least two
pairwise distances are equal.
Bridge: connects ultrametric_geometry to clustering algorithms.
-/

/-
The prefix gap satisfies the ultrametric inequality.
Bridge: connects to certified_robustness (perturbation stability).
-/

/-! ## Section 18: Normalized Entropy Properties -/




open OracleTrace in
theorem solution    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (u v w : List α)
    (hstrict : prefixDist ρ u v < prefixDist ρ v w) :
    prefixDist ρ u w = prefixDist ρ v w := by
  -- Since ρ ∈ (0,1), ρ^· is strictly antitone on ℕ. From hstrict : ρ^lcvpLen(u,v) < ρ^lcvpLen(v,w), we get lcvpLen(v,w) < lcvpLen(u,v).
  have h_lcvpLen : lcvpLen v w < lcvpLen u v := by
    unfold prefixDist at hstrict;
    rwa [ pow_lt_pow_iff_right_of_lt_one₀ hρ0 hρ1 ] at hstrict;
  have h_lcvpLen2 : lcvpLen u w ≤ lcvpLen v w := by
    have := lcvpLen_ge_min_of_triangle v u w;
    rw [ min_le_iff ] at this;
    exact this.resolve_left ( by linarith [ lcvpLen_symmetric u v ] );
  have h_lcvpLen3 : lcvpLen v w ≤ lcvpLen u w := by
    apply le_trans (by
    exact le_min h_lcvpLen.le le_rfl) (lcvpLen_ge_min_of_triangle u v w);
  exact congr_arg _ ( le_antisymm h_lcvpLen2 h_lcvpLen3 )
