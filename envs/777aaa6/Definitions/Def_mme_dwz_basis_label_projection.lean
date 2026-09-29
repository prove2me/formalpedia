-- Prove2me | Definitions.Def_mme_dwz_basis_label_projection
-- name    : mme_dwz_basis_label_projection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T10:03:28.010281+00:00
-- url     : https://prove2.me/theorems/69f3d57c-ba50-447c-a9a7-a77ac56e980d
-- title:
--   Diagonal projection on a labelled tensor-mode basis
-- statement:
--   Fix a finite collection of labels on a basis of a vector space. For any finite set of retained labels, this definition gives the diagonal linear projection that fixes precisely the basis vectors with retained labels and sends every other basis vector to zero. In the DWZ Hole Lemma application, the basis is the grouped standard-Z basis and the label is its useful-block address; hence this is literal variable zeroing, not a cardinality surrogate.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 5 (Hole Lemma) and Definitions 5.4 and 6.3 (PDF pp.47 and 53 / printed pp.46 and 52), formalizing the Z-variable restriction by useful-block labels.

import Definitions.Def_mme_dwz_broken_standard_obj

open MME Module

universe u

namespace MME.DWZComponentRestriction

set_option autoImplicit false
set_option warningAsError true

/-- Diagonal projection onto the basis vectors whose labels lie in `blocks`. -/
noncomputable def basisLabelProjection
    {ι β V : Type*} {K : Type u} [Field K]
    [AddCommMonoid V] [Module K V] [DecidableEq β]
    (b : Basis ι K V) (label : ι → β) (blocks : Finset β) : V →ₗ[K] V :=
  b.constr K (fun i ↦ if label i ∈ blocks then b i else 0)

end MME.DWZComponentRestriction


