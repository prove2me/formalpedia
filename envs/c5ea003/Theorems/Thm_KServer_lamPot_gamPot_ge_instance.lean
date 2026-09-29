-- Prove2me | Theorems.Thm_KServer_lamPot_gamPot_ge_instance
-- name    : KServer.lamPot_gamPot_ge_instance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T16:36:56.903025+00:00
-- url     : https://prove2.me/theorems/559c82cb-ece1-4af4-be71-9adf2a08c17e
-- title:
--   Instantiating the auxiliary potentials Lambda and Gamma
-- statement:
--   The two auxiliary potentials $\Lambda_{w,x}$ and $\Gamma_{w,x}$ are, like $\Psi$, defined as suprema over free witnesses, so each of them is bounded below by every instance of the expression it maximises. Writing both bounds out with their inner two-point shadows also instantiated gives, for **all** points $p,q,b,b',c,c',e,e',d,d',f$:
--
--   $$\Lambda_{w,r}\;\ge\;\bigl(-rp + pb + pb' - w(r,b,b')\bigr) + \bigl(-rq + qc + qc' - w(r,c,c')\bigr) - w(r,p,q) + \bigl(ee' - w(r,e,e')\bigr)$$
--
--   and
--
--   $$\Gamma_{w,r}\;\ge\;\bigl(-rp + pb + pb' - w(r,b,b')\bigr) + rq + \bigl(dd' - w(r,q,d) - w(r,q,d')\bigr) + \bigl(qf - w(r,p,f)\bigr).$$
--
--   ## Role
--
--   This is the counterpart, for $\Lambda$ and $\Gamma$, of the instantiation lemma already available for the lazy potential $\Psi$. Ten of the twelve cases of the update property for $\hat\Psi = \max\{\Psi,\Lambda,\Gamma\}$ finish by exhibiting the rearranged expression as an instance of $\Psi_{w,r}$; the two remaining cases finish instead by exhibiting it as an instance of $\Lambda_{w,r}$ or of $\Gamma_{w,r}$, which is exactly what the two halves of this statement provide.
--
--   In each half the innermost supremum $\tilde w(r,p) \ge pb + pb' - w(r,b,b')$ is instantiated separately from the outer one, so the caller may choose the witnesses of the inner and outer suprema independently — the case analysis does exactly that, the inner witnesses coming from the branch of the update formula and the outer ones from the servers' positions.
--
--   **Formalization note.** Both halves are `le_csSup` applied to the defining range, which requires that range to be bounded above. For $\Lambda$ this follows termwise from the triangle inequality together with the lower bound $w(r,y,z) \ge$ (sum of the distances from the base configuration) $- $ (the perimeter terms); for $\Gamma$ the corresponding bound needs the two occurrences of the auxiliary point $q$ to cancel exactly, since $+\,rq$ appears with a positive sign and is only paid for by the two work-function values $w(r,q,d)$ and $w(r,q,d')$.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Section 3: the definitions of the auxiliary potentials Lambda and Gamma, used in this instantiated form in the two cases of Lemma 4 that do not reduce to an instance of Psi.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem lamPot_gamPot_ge_instance (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r : M) :
    (∀ p q b b' c c' e e' : M,
      (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
        + (-dist r q + (dist q c + dist q c' - workFnU C₀ σ ![r, c, c']))
        - workFnU C₀ σ ![r, p, q] + dist e e' - workFnU C₀ σ ![r, e, e']
        ≤ lamPot C₀ σ r)
    ∧ (∀ p q d d' f b b' : M,
      (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
        + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
        + dist q f - workFnU C₀ σ ![r, p, f]
        ≤ gamPot C₀ σ r) := by sorry

end KServer
