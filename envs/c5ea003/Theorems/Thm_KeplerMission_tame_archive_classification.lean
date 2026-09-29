-- Prove2me | Theorems.Thm_KeplerMission_tame_archive_classification
-- name    : KeplerMission.tame_archive_classification
-- status  : Open
-- author  : @Minghui
-- created : 2026-09-27T03:24:51.693008+00:00
-- url     : https://prove2.me/theorems/2143b78a-ab22-4b58-8074-61e20f39fd27
-- title:
--   Exhaustive tame hypermap archive
-- statement:
--   Every fixed archive row decodes to a good face list. Every tame finite hypermap is represented by one of those rows, allowing reversal of orientation. Representation requires exact node labels, unique directed darts, edge reversal and complete face cycles. This is a coverage theorem, not merely a claim that archived rows are tame. The reported 18,762 matches the [AFP 2013-12-11 archive](https://isa-afp.org/release/afp-Flyspeck-Tame-2013-12-11.tar.gz): 9 triangular, 1,105 quadrilateral, 15,991 pentagonal and 1,657 hexagonal cases. The [AFP entry](https://isa-afp.org/entries/Flyspeck-Tame.html) records a change of tameness constants and archive on 3 July 2014. The final archive has 19,715 rows: 9 + 1,253 + 16,080 + 2,373; the pinned [make_archive.hl](https://github.com/flyspeck/flyspeck/blob/1ce0353008eba83d3c76ae9a25c3c242e4802d53/formal_graph/archive/make_archive.hl#L38) explicitly records this July-2014 count. Exact permutation comparison shows all 18,762 older classes retained and 953 added, with no duplicate or mirror-equivalent rows within either archive. The mission uses the final accompanying archive, whose source SHA-256 is `703ea865a124aa69f0ee12d94df7065bbbf5701a3085776e24632d14493474db`. These are candidate graphs: the classification is coverage, not a claim that every stored row is tame or geometrically realizable (primary §7.2).
--
--   $$\operatorname{ArchiveWellFormed}\ \land\ \forall H,\ \operatorname{Tame}(H)\Longrightarrow\exists L\in\mathcal G,\ \operatorname{Rep}(L,H)\lor\operatorname{Rep}(L,H^{\mathrm{op}}).$$
--
--   Here G is the fixed decoded archive, Rep is the complete face-list representation relation, and H^op reverses orientation.
--
--   **Source.** Hales et al., A Formal Proof of the Kepler Conjecture (2017), https://doi.org/10.1017/fmp.2017.1, §§7–8 pp.17–21; Blueprint Theorem8.38 WTEMDTA (extended PDF p.312); AFP Flyspeck-Tame Computation/Completeness.thy:completeness; formal_graph/archive/archive_all.ml.
--
--   **Formalization note.** Source-derived interface or explicitly identified analytic corollary; no proof of the target is supplied by defining its proposition.
-- source:
--   Hales et al., A Formal Proof of the Kepler Conjecture (2017), https://doi.org/10.1017/fmp.2017.1; §§7–8 pp.17–21; Blueprint Theorem8.38 WTEMDTA (extended PDF p.312); AFP Flyspeck-Tame Computation/Completeness.thy:completeness; formal_graph/archive/archive_all.ml; https://github.com/flyspeck/flyspeck/blob/1ce0353008eba83d3c76ae9a25c3c242e4802d53/text_formalization/general/the_main_statement.hl; https://publicationsthomashales.wordpress.com/wp-content/uploads/2016/03/densespherepackings.pdf

import Definitions.Def_Kepler_MissionContracts
set_option autoImplicit false

namespace KeplerMission
theorem tame_archive_classification : TameArchiveClassification := by sorry
end KeplerMission
