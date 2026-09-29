-- Prove2me | Theorems.Thm_mme_dwz_prime_hash_budget_to_actual_standard_products
-- name    : mme_dwz_prime_hash_budget_to_actual_standard_products
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T10:31:39.531975+00:00
-- url     : https://prove2.me/theorems/b9e8ac16-ad7e-4b3b-b517-e62148e08a8a
-- title:
--   Concrete prime-hash budget for multiple actual fourth-level standard products
-- statement:
--   Let $K$ be a field, $q,N>0$, and $r\geq0$ an integer. Let $C=[k]$ be full component labels. For each $c\in C$, choose $I_c,J_c,L_c\in\{0,\ldots,8\}$ summing to $8$, and let $T_c$ be the actual canonical constituent of the balanced fourth power of $\mathrm{CW}_q$. Choose positive integers $d_c$, nonnegative counts $\pi_c(a)$ summing to $d_c$, and $m_c\geq0$. Put $n_c=d_cm_c$, and require
--   $$
--   \pi_c(a)>0\ \Longrightarrow\ a\leq L_c\leq a+4.
--   $$
--   Set $\mu_{Z,c}(a)=m_c\pi_c(a)$. Prescribe X and Y boundary tables satisfying $\mu_{Z,c}(a)=\mu_{Y,c}(4-a)$ when $I_c=0$, and $\mu_{Z,c}(a)=\mu_{X,c}(4-a)$ when $J_c=0$.
--
--   Let $\mathcal T\subseteq\mathcal A$ be finite families of component words $c_j:[N]\to C$, and write their coarse addresses as $(X_j,Y_j,Z_j)$. Targets have common coarse marginal counts. The ambient family represents every supported coarse address with those marginals and contains no duplicated coarse address. For each target, supply a component-preserving bijection
--   $$
--   [N]\simeq\bigsqcup_{c\in C}[n_c].
--   $$
--   The corresponding full joint-type condition is required only of targets.
--
--   Let $M>8$ be an odd prime, let $[H+1]\simeq[N]$, and let $S\subseteq\{0,\ldots,\lfloor M/2\rfloor-1\}$ contain no nonconstant three-term arithmetic progression. Suppose each target shares its X address with at most $D$ ambient members and its Y address with at most $D$ ambient members.
--
--   For every target $j$ and every fine Z-word having its coarse grades and complete componentwise left-square profile $\mu_{Z,c}$, suppose at most $C_0$ other targets are compatible with that word. Compatibility requires the same coarse Z address and the prescribed split histograms on the boundary components only. Assume
--   $$
--   4D\leq M,\qquad 8C_0\leq M,\qquad
--   8M^2r(3N+2)\leq3|\mathcal T|\,|S|.
--   $$
--   Then the actual atomic CW power restricts to the requested number of canonical prescribed-Z products:
--   $$
--   \mathrm{CW}_q^{\otimes4N}\ \longrightarrow
--   \left(\bigotimes_{c\in C}T_c^{\otimes n_c}[\pi_c]\right)^{\oplus r}.
--   $$
--   The arrow denotes modewise linear tensor restriction, and each prescribed projection uses the actual canonical constituent basis and literal left-square grade.
--
--   No retention events, event cardinalities, or pair-probability bounds are assumed: these are supplied by the concrete prime-field affine hash. The selected family and all hole masks come from one common hash state, and repair preserves the original masks and output multiplicity. The case $r=0$ is included. Proving large target families, the compatible-degree estimate, useful progression-free set sizes, and the asymptotic value bound remains separate.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 3.10 (affine hashes and Lemma 3.11), Section 6.1 (boundary filtering and common standard form), Section 6.2 (Claim 6.8 and the final multiplicity estimate), and Section 5.2 Corollary 5.11. https://arxiv.org/html/2210.10173v5#S6.SS2 . Derived finite fourth-level specialization with explicit natural prime-modulus budget; it does not establish entropy or compatible-degree asymptotics.

import Theorems.Thm_mme_dwz_supported_address_hash_event_counts
import Theorems.Thm_mme_dwz_fourth_many_standard_products_restrict_of_finite_hash_budget
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open MME MME.TensorObj MME.StothersFourth MME.DWZSimultaneous
  MME.DWZComponentRestriction MME.DWZRestrictedValue MME.CompleteSplit.CWFourth
  MME.CompleteSplit MME.DWZStep1Support Module PiTensorProduct BigOperators
open scoped Classical
universe u
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_dwz_prime_hash_budget_to_actual_standard_products
    {K : Type u} [Field K] (q N H modulus R k r : ℕ)
    [Fact modulus.Prime] (hq : 0 < q) (hN : 0 < N)
    (I J L : Fin k → Fin 9)
    (p : Fin k → IntegerZSplitProfile 5) (m : Fin k → ℕ)
    (component : Fin R → Fin N → Fin k) (shape : Fin k → Fin 3 → ℕ)
    (hshape : ∀ c i, shape c i = (cwFourthBlockType (I c) (J c) (L c) i).val)
    (hsum : ∀ c, shape c 0 + shape c 1 + shape c 2 = 8)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ)
    (hmu : ∀ c a, mu 2 c a = (p c).count a * m c)
    (hmuX : ∀ c, shape c 0 = 0 → ∀ a, mu 2 c a = mu 1 c (Fin.rev a))
    (hmuY : ∀ c, shape c 1 = 0 → ∀ a, mu 2 c a = mu 0 c (Fin.rev a))
    (marginal : Fin 3 → ℕ → ℕ)
    (targets ambient : Finset (Fin R)) (hsub : targets ⊆ ambient)
    (hmarginal : ∀ a ∈ targets, SameMarginal marginal (owner component shape a))
    (hcomplete : ∀ a : CoarseAddress N, Supported 8 a → SameMarginal marginal a →
      ∃ b ∈ ambient, owner component shape b = a)
    (hinjective : Set.InjOn (owner component shape) (ambient : Set (Fin R)))
    (positions : ∀ a : Fin R, a ∈ targets →
      (Fin N ≃ Σ c, Fin ((p c).length (m c))))
    (hcell : ∀ a (ha : a ∈ targets) c r, component a ((positions a ha).symm ⟨c,r⟩) = c)
    (hsupport : ∀ c a, 0 < (p c).count a →
      a.val ≤ (L c).val ∧ (L c).val ≤ a.val + 4)
    (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (modulus / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd modulus)
    (hmodulus : 8 < modulus)
    (degree compatibleDegree : ℕ)
    (hxyBudget : 4 * degree ≤ modulus) (hzBudget : 8 * compatibleDegree ≤ modulus)
    (hx : ∀ a ∈ targets,
      (ambient.filter (fun b ↦ owner component shape b 0 = owner component shape a 0)).card ≤ degree)
    (hy : ∀ a ∈ targets,
      (ambient.filter (fun b ↦ owner component shape b 1 = owner component shape a 1)).card ≤ degree)
    (hzCard : ∀ a ∈ targets, ∀ f : FineWord 3 N,
      Graded component shape a 2 f ∧ Profile component fourthLeftTag mu a 2 f →
      (targets.filter (fun b ↦ b ≠ a ∧ ZCompatible component shape fourthLeftTag mu b f)).card ≤
        compatibleDegree)
    (hbudget : 8 * modulus ^ 2 * (r * (3 * N + 2)) ≤
      3 * targets.card * S.card) :
    TensorObj.Restrict
      (bigAdd (fun _ : Fin r ↦ kronFin k (fun c ↦ prescribedZPower
        (cwFourthConstituent K q (I c) (J c) (L c))
        (constituentBasis K q (I c) (J c) (L c) 2)
        (fun a : LiftedCoarseCoordinate.{u} q (L c) ↦ cwSquarePairGrade q a.down.val.1)
        (p c) (m c))))
      ((CWObj K q).kronPow (N * 4)) := by sorry
