-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedChunk21_valid
-- name    : Couret.InterIA.SingletonNecessity.mixedChunk21_valid
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:52:26.495229+00:00
-- url     : https://prove2.me/theorems/1fdf0906-2567-4e3d-9124-338642543578
-- title:
--   Mixed relation certificate validity for fixed block 21
-- statement:
--   Let $C_{21}$ denote the fixed finite certificate list named `mixedChunk21` in MatchingCertificateData; its entries are the specified stored tuples, with no additional input parameters.
--
--   Work in the free abelian group $V=\mathbb Z^6$, with standard basis $e_0,\ldots,e_5$. Define seven label vectors by $\ell_0=0$ and $\ell_r=e_{r-1}$ for $1\le r\le6$. A certificate is a tuple $c=(p,i,j,\lambda)$, where $p$ is a finite list of natural numbers, $i,j\in\mathbb N$, and $\lambda$ is a finite list of integers.
--
--   For the mixed relation system, use the ordered lists
--   $$
--   L=(e_0,e_1,e_2,e_0+e_1,e_0+e_2,e_1+e_2,2e_0),
--   $$
--   $$
--   R=(e_3,e_4,e_5,e_3+e_4,e_3+e_5,e_4+e_5,2e_3).
--   $$
--   For $p=(p_0,\ldots,p_{s-1})$, let $\mathcal R(p)$ be the ordered row list beginning with
--   $$
--   2(e_0-e_1),\qquad2(e_3-e_4),\qquad2(e_2-e_5),
--   $$
--   and followed by $L_k-R_{p_k}$ for $0\le k<\min(7,s)$, in increasing order of $k$. Here $R_q$ is interpreted as the zero vector if $q\ge7$. Thus $m(p)=|\mathcal R(p)|=3+\min(7,s)$; the truncation and zero default are part of the relation-list definition.
--
--   Every certificate $c=(p,i,j,\lambda)$ occurring in $C_{21}$ satisfies all the tests of the mixed validity predicate:
--   $$
--   i<j<7,\qquad |\lambda|=m(p),\qquad\sum_{t=0}^{m(p)-1}\lambda_t\,\mathcal R(p)_t=\ell_i-\ell_j.
--   $$
--
--   Equivalently, the conjunction of these tests over the named fixed block has Boolean value true. This certifies the recorded mixed relation identities for that block. The validity predicate does not separately test that $p$ is a permutation, its length, uniqueness of its entries, or coverage of any larger enumeration; such properties require separate statements.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/MatchingCertificateData.lean, lines 2315–2315; source file SHA-256 281f2db6030f883e89d5aa00658e16116a8de5187f3c58c3d03bf50c9b44685c; theorem Couret.InterIA.SingletonNecessity.mixedChunk21_valid

import Definitions.Def_Couret_MatchingCertificateData_656be71337d8
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Definitions.Def_Couret_MatchingCertificateCore_fbb5abd3e874

set_option autoImplicit false

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000

namespace Couret.InterIA.SingletonNecessity

theorem mixedChunk21_valid : mixedChunk21.all (valid true) = true := by sorry












































































































































































































































end Couret.InterIA.SingletonNecessity
