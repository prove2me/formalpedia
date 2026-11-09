-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_region_test_by_sat
-- name    : WitnessIsolation.AffineCollapse.region_test_by_sat
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:58.51036+00:00
-- url     : https://prove2.me/theorems/a23cd28d-4533-4fe7-abe7-8eb259b0ab52
-- title:
--   Lemma 5.1 — Region test by SAT
-- statement:
--   Let D have tv declared variables, in t blocks of width v, and let each block have one or two explicitly known points, defining a product K. A concrete polynomial-size circuit produces 2t+1 nonadaptive SAT queries, each declaring exactly t variables. Their exact SAT answers determine
--
--   $$|\operatorname{Sol}(D)\cap K|=1.$$
--
--   There are fixed natural coefficients and exponents bounding both the query-description cap and the query compiler by c(s+v+t+2)^k, where s is the actual-description cap for D. These bounds hold before any SAT-answering circuit is supplied. If A is a circuit giving the correct satisfiability answer on all queries produced from eligible inputs, the resulting test has gate count at most
--
--   $$c(s+v+t+2)^k(|A|+1).$$
--
--   The assertion includes the query compiler, well-formedness and dimension of every query, the Boolean decision formula, and a genuine implementing test circuit. It covers duplicate listed points, zero blocks and zero-width blocks. This preserves the linear cost of the smaller SAT circuit needed by the transfer theorem.
--
--   Differences from the source:
--   - encoding: one or two listed points per block → two points with equality allowed, encoded with the padded D description as circuit inputs; reason: equal pairs represent exactly singleton lists; this includes every source instance
--   - encoding: fixed polynomial construction/query lengths and poly(|D|,v,t)(T+1) test size → uniform existential c,k, a query-producing DAG circuit and a test circuit with bound c(s+v+t+2)^k(T+1); reason: all operations have actual circuit syntax; the cap records bit length, and the shared monomial dominates the finitely many unspecified source polynomials
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), Lemma 5.1, printed p. 10, PDF p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/346.pdf; PDF SHA256 969057d4c1837a5ebf1d45c70a14c1d66f0d76610c6233f151e2402e7611f42e

import Definitions.Def_WitnessIsolation_AffineCollapse_regions

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace WitnessIsolation.AffineCollapse

/-- Lemma 5.1. A concrete polynomial-size query-producing circuit precedes all SAT answers. -/
theorem region_test_by_sat :
    ∃ c k : ℕ, 1 ≤ c ∧ ∀ s v t : ℕ,
      let b := c*(s+v+t+2)^k
      ∃ compiler : Circuit (regionInputWidth s v t) ((2*t+1)*paddedWidth b),
        compiler.size ≤ c*(s+v+t+2)^k ∧
        (∀ (h : Bits (paddedWidth s)) (D : Description), decodedPadded s h = some D →
          D.inputs = t*v → ∀ p q : Fin t → Bits v,
          (∀ j : Fin (2*t+1), ∃ R,
            decodedPadded b (queryOutput compiler (regionInput h p q) j) = some R ∧ R.inputs = t) ∧
          (RegionSingleton D p q ↔ answersAccept (fun j => decide
            (CappedSAT b t (queryOutput compiler (regionInput h p q) j))))) ∧
        (∀ A : Circuit (paddedWidth b) 1,
          (∀ (h : Bits (paddedWidth s)) D, decodedPadded s h = some D → D.inputs = t*v →
            ∀ (p q : Fin t → Bits v) j,
              A.accepts (queryOutput compiler (regionInput h p q) j) ↔
                CappedSAT b t (queryOutput compiler (regionInput h p q) j)) →
          ∃ test : Circuit (regionInputWidth s v t) 1,
            test.size ≤ c*(s+v+t+2)^k*(A.size+1) ∧
            ∀ (h : Bits (paddedWidth s)) D, decodedPadded s h = some D → D.inputs = t*v →
              ∀ p q : Fin t → Bits v,
                test.accepts (regionInput h p q) ↔ RegionSingleton D p q) := by sorry

end WitnessIsolation.AffineCollapse
