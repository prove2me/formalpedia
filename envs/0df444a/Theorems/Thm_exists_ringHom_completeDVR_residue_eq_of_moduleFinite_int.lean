-- Prove2me | Theorems.Thm_exists_ringHom_completeDVR_residue_eq_of_moduleFinite_int
-- name    : exists_ringHom_completeDVR_residue_eq_of_moduleFinite_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/8f07757b-0699-5d17-9edc-723854b71fbe
-- title:
--   Embedding a ℤ-finite domain into a complete DVR
-- statement:
--   Let $R$ be a commutative ring which is an integral domain of characteristic zero and finitely generated as a $\mathbb{Z}$-module, let $p$ be a prime number, let $F$ be a field of characteristic $p$, and let $\pi \colon R \to F$ be a ring homomorphism. The assertion is the existence of the following data: a commutative ring $\mathcal{O}$ which is an integral domain, a discrete valuation ring, adically complete with respect to its maximal ideal $\mathfrak{m}_{\mathcal{O}}$, with finite residue field $\mathcal{O}/\mathfrak{m}_{\mathcal{O}}$ and of characteristic zero; a ring homomorphism $\psi \colon R \to \mathcal{O}$; a field $F'$ equipped with an $F$-algebra structure; and a ring homomorphism $\iota \colon \mathcal{O}/\mathfrak{m}_{\mathcal{O}} \to F'$, such that $\psi$ is injective, the preimage $\psi^{-1}(\mathfrak{m}_{\mathcal{O}})$ equals $\ker \pi$, the image of $p$ in $\mathcal{O}$ lies in $\mathfrak{m}_{\mathcal{O}}$, and for every $x \in R$ one has $\iota(\psi(x) \bmod \mathfrak{m}_{\mathcal{O}}) = \pi(x)$ in $F'$, the right-hand side being taken via the structure map $F \to F'$. Thus $\pi$ is recovered, after the extension $F \to F'$, from reduction of $\psi$ modulo $\mathfrak{m}_{\mathcal{O}}$.
--
--   This is the standard passage from an abstract $\mathbb{Z}$-finite coefficient domain with a characteristic-$p$ character to a $p$-adic coefficient ring: the fraction field of $R$ is a number field, $\ker \pi$ is a prime above $p$, and $\mathcal{O}$ may be taken to be the completion of the ring of integers at a prime lying over it. It supplies the complete discrete valuation coefficient ring needed in [`WeierstrassCurve.isModularModelOfLevel_div_of_isGoodPrimeFor_of_dvd_of_not_sq_dvd`](thm.html#WeierstrassCurve.isModularModelOfLevel_div_of_isGoodPrimeFor_of_dvd_of_not_sq_dvd), where Hecke eigenvalues living in a $\mathbb{Z}$-finite ring must be compared with a mod-$p$ system.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_ringHom_completeDVR_residue_eq_of_moduleFinite_int.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem exists_ringHom_completeDVR_residue_eq_of_moduleFinite_int
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] [Module.Finite ℤ R]
    (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharP F p] (π : R →+* F) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
        (_ : Finite (IsLocalRing.ResidueField O)) (_ : CharZero O)
        (ψ : R →+* O) (F' : Type) (_ : Field F') (_ : Algebra F F')
        (ι : IsLocalRing.ResidueField O →+* F'),
      Function.Injective ψ ∧
      Ideal.comap ψ (IsLocalRing.maximalIdeal O) = RingHom.ker π ∧
      (p : O) ∈ IsLocalRing.maximalIdeal O ∧
      ∀ x, ι (IsLocalRing.residue O (ψ x)) = algebraMap F F' (π x) := by sorry
