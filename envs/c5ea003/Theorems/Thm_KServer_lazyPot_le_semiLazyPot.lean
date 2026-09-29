-- Prove2me | Theorems.Thm_KServer_lazyPot_le_semiLazyPot
-- name    : KServer.lazyPot_le_semiLazyPot
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T16:54:33.767951+00:00
-- url     : https://prove2.me/theorems/742f7e93-8c9a-4d27-83b3-8eb9f884c0f2
-- title:
--   The lazy potential at any point is below the semi-lazy potential at the last request
-- statement:
--   Let $w$ be a work function for three servers whose last request is $r$. Then for **every** point $s$ of the metric space,
--
--   $$\Psi_{w,s}\;\le\;\hat\Psi_{w,r},$$
--
--   where $\Psi_{w,x} = \hat w(x) + \dot w(x)$ is the lazy potential and $\hat\Psi_{w,x} = \max\{\Psi_{w,x}, \Lambda_{w,x}, \Gamma_{w,x}\}$ is the semi-lazy potential.
--
--   ## Role
--
--   This is the technical heart of the Bein–Chrobak–Larmore analysis of the Work Function Algorithm for three servers, and it holds in an **arbitrary** metric space — no planarity, no Manhattan geometry. It is what converts the local update property required by the potential-function criterion into the single global hypothesis $\hat\Psi_{w,r} \le \Psi_{w,r}$, which then has to be checked space by space. Concretely, the update property
--
--   $$\Psi_{\mu,s} + r_s(w) \;\le\; \Psi_{w,r}$$
--
--   follows from this lemma together with the identity $\hat\mu(s) + r_s(w) = \hat w(s)$ relating the shadow before and after the request: the left-hand side equals $\Psi_{w,s}$, which this lemma bounds by $\hat\Psi_{w,r}$, and the hypothesis on the space finishes the job.
--
--   The statement is deceptively short. Its proof compares the potential at the *arbitrary* point $s$ with the potential at the *last requested* point $r$, and the only handle on the difference is the recursion
--
--   $$w(s,x,y) \;=\; \min\{\,w(x,y) + rs,\;\; w(s,y) + rx,\;\; w(s,x) + ry\,\}$$
--
--   which expresses a work-function value at a configuration not containing $r$ in terms of values at configurations that do contain $r$. The expression for $\Psi_{w,s}$ contains three such values — $w(s,b,b')$, $w(s,p,d)$ and $w(s,p,d')$ — so the recursion has to be applied three times, giving $3^3 = 27$ combinations of branches. The symmetries $b \leftrightarrow b'$ and $d \leftrightarrow d'$ cut these down to twelve genuinely different computations. In eight of them the resulting expression is, after triangle inequalities alone, an instance of $\Psi_{w,r}$; two more need the quasiconvexity of the work function to rematch a pair of terms; and the last two land on $\Lambda_{w,r}$ and $\Gamma_{w,r}$ respectively — which is the reason the semi-lazy potential has to carry those two extra maxima at all. Two of the branches close only as the *average* of two instances of $\Psi_{w,r}$, which is legitimate because the bound being proved is linear.
--
--   **Formalization note.** All twenty-seven branches are carried out; the two symmetries are realised not by a meta-argument but by applying the same twelve case lemmas with the corresponding arguments transposed, which is sound because the statement of each case lemma is stated for free points. Reducing the potential inequality to the pointwise inequality over the seven free witnesses is a separate lemma, as are the instantiation lemmas for $\Psi$, $\Lambda$ and $\Gamma$.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Lemma 4: 'Let w be a work function over M with last request r. Then Psi_{w,s} <= hatPsi_{w,r} for all s in M.'

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem lazyPot_le_semiLazyPot (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r s : M) :
    lazyPot C₀ (σ ++ [r]) s ≤ semiLazyPot C₀ (σ ++ [r]) r := by sorry

end KServer
