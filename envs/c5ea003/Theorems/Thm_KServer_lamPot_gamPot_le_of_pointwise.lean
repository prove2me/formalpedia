-- Prove2me | Theorems.Thm_KServer_lamPot_gamPot_le_of_pointwise
-- name    : KServer.lamPot_gamPot_le_of_pointwise
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T17:30:06.541938+00:00
-- url     : https://prove2.me/theorems/fd41e249-d317-452c-a3f9-271e6e8247a6
-- title:
--   Bounding the auxiliary potentials by bounding every instance
-- statement:
--   The auxiliary potentials $\Lambda_{w,r}$ and $\Gamma_{w,r}$ are suprema over free witnesses, with an inner two-point shadow nested inside. To bound either of them above by a number $B$, it therefore suffices to bound every instance:
--
--   $$\Lambda_{w,r} \le B \quad\Longleftarrow\quad \bigl(-rp + pb + pb' - w(b,b')\bigr) + \bigl(-rq + qc + qc' - w(c,c')\bigr) - w(p,q) + ee' - w(e,e') \;\le\; B \ \text{ for all } p,q,b,b',c,c',e,e',$$
--
--   and similarly
--
--   $$\Gamma_{w,r} \le B \quad\Longleftarrow\quad \bigl(-rp + pb + pb' - w(b,b')\bigr) + rq + \bigl(dd' - w(q,d) - w(q,d')\bigr) + \bigl(qf - w(p,f)\bigr) \;\le\; B \ \text{ for all } p,q,d,d',f,b,b'.$$
--
--   ## Role
--
--   This is the entry point to the proofs that $\Lambda_{w,r}, \Gamma_{w,r} \le \Psi_{w,r}$ in the city-block plane: those proofs begin "pick $p, b, b', q, c, c', e, e'$ such that $\Lambda_{w,r} = \dots$" and then argue about the chosen points, and this lemma is what licenses that opening. It is the counterpart, for the auxiliary potentials, of the corresponding reduction for the lazy potential.
--
--   **Formalization note.** Suprema in a general metric space need not be attained, so the witnesses are extracted only approximately: for each $\varepsilon > 0$ the outer supremum and each inner shadow are realised to within $\varepsilon/3$ (resp. $\varepsilon/2$ for $\Gamma$, which has only one inner shadow), and the conclusion is assembled by `le_of_forall_pos_le_add`. Unlike the corresponding lemma for the lazy potential, the extractions here are independent of one another: the two inner shadows of $\Lambda$ are taken at points supplied by the outer witness, but not at points supplied by each other. Each extraction requires the corresponding set to be bounded above, which comes from the unit-rate growth of the work function.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Section 4, the opening of the proofs of Lemmas 5 and 6: 'Pick p, b, b', q, c, c', e, e' such that Lambda_{w,r} = ...' and 'Pick points p, b, b', q, d, d', f such that Gamma_{w,r} = ...'.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem lamPot_gamPot_le_of_pointwise (M : Type) [MetricSpace M] (C₀ : Config 3 M)
    (σ : List M) (r : M) (B : ℝ)
    (hlam : ∀ p q b b' c c' e e' : M,
      (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
        + (-dist r q + (dist q c + dist q c' - workFnU C₀ σ ![r, c, c']))
        - workFnU C₀ σ ![r, p, q] + dist e e' - workFnU C₀ σ ![r, e, e'] ≤ B)
    (hgam : ∀ p q d d' f b b' : M,
      (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
        + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
        + dist q f - workFnU C₀ σ ![r, p, f] ≤ B) :
    lamPot C₀ σ r ≤ B ∧ gamPot C₀ σ r ≤ B := by sorry

end KServer
