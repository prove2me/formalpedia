-- Prove2me | Theorems.Thm_mme_Ctensor_one_H_one_family_certificate_mono_restrict
-- name    : mme_Ctensor_one_H_one_family_certificate_mono_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:46:04.10863+00:00
-- url     : https://prove2.me/theorems/41a4793a-3f73-4e28-827a-40b48d53b136
-- title:
--   C-tensor outer-family certificates are monotone under source restriction
-- statement:
--   Suppose a tensor $T$ restricts to a direct sum of $A$ C-tensor stars, each with $H$ inner components and common component volume $v$. If $T$ is itself a restriction of a tensor $S$, then the same outer-family certificate holds for $S$. Thus finite primary-hash C-tensor families can be transported backward through exact component routers and tensor isomorphisms without changing their multiplicity or volume parameters.
-- source:
--   Functoriality of Strassen restriction under composition; used in the Coppersmith--Winograd and Duan--Wu--Zhou laser-method extraction pipelines.

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_tensor_quotient

open MME

universe u

set_option autoImplicit false

theorem mme_Ctensor_one_H_one_family_certificate_mono_restrict
    {K : Type u} [Field K]
    {S T : TensorObj K 3} {A H volume : ℕ}
    (stars : Nonempty (CTensorOneHOneFamilyCertificate T A H volume))
    (hTS : TensorObj.Restrict T S) :
    Nonempty (CTensorOneHOneFamilyCertificate S A H volume) := by
  sorry
