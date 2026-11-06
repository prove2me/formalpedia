-- Prove2me | Theorems.Thm_ZeroOneExpansion_lemma_12
-- name    : ZeroOneExpansion.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:08.061203+00:00
-- url     : https://prove2.me/theorems/5568970c-95d2-44d4-9957-bc0f40e21c9b
-- title:
--   Lemma 12 — $0<|S_n|=12^n-\sum_r A_{r,r}<12^n=|V_n|/2$
-- statement:
--   For every $n\ge1$,
--   $$0<|S_n|=12^n-\sum_{r=0}^nA_{r,r}<12^n=\frac{|V_n|}{2}.$$
--
--   In particular $S_n$ is admissible in the definition of $h(G_n)$.
--
--   Differences from the source:
--   - encoding: |S_n| = 12^n − Σ A_{r,r} → the identity in ℤ; reason: no truncated natural-number subtraction
--   - encoding: 12^n = |V_n|/2 → Nat.card (vertices of P_n) = 2·12^n; reason: the vertex set of G_n is V_n (Fact 3); multiplying by 2 avoids division
--   - encoding: S_n ⊆ V_n, with I(u), J(u) over [n] → Sn n, a set of vertices of P_n (Grunbaum2003.PolytopeVertex (Pn n)), with I, J as Iset/Jset over Fin n (0-based); reason: the vertices of P_n are V_n (Fact 3); [n] relabelled 0-based; same instances
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), Lemma 12, display (2), p.7

import Mathlib
import Definitions.Def_ZeroOneExpansion_Sn

set_option autoImplicit false

namespace ZeroOneExpansion

/-- **Lemma 12** (Yang, *0/1-Polytopes with Exponentially Small Edge Expansion*, arXiv:2608.01870, p.7, display (2)). For every `n ≥ 1`,
`0 < |Sn| = 12^n − ∑_{r=0}^n A_{r,r} < 12^n = |Vn|/2`.

**Formalization Note** `|Sn|` is `Set.ncard` of `Sn` (a set of vertices of `Gn`). The identity is in
`ℤ`, so the subtraction does not truncate. `12^n = |Vn|/2` is written `|Vn| = 2 · 12^n`, with `|Vn|`
the number of vertices of `Gn` (`Nat.card` of `Grunbaum2003.PolytopeVertex (Pn n)`), which is `Vn` by
Fact 3. -/
theorem lemma_12 (n : ℕ) (hn : 1 ≤ n) :
    0 < (Sn n).ncard ∧
    ((Sn n).ncard : ℤ) = 12 ^ n - ∑ r ∈ Finset.range (n + 1), (Acount n r r : ℤ) ∧
    (Sn n).ncard < 12 ^ n ∧
    Nat.card (Grunbaum2003.PolytopeVertex (Pn n)) = 2 * 12 ^ n := by sorry

end ZeroOneExpansion
