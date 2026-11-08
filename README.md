# The orthogonal boundary-point art gallery problem is ∃ℝ-complete, in Lean 4

This repository contains a Lean 4 formalization of material in a forthcoming manuscript entitled
*The Orthogonal Art Gallery Problem is ∃ℝ-complete*.

Lean proves that the **boundary-point** art gallery problem (the guards must lie on the boundary
and see the whole closed polygon) remains `∃ℝ`-complete for **orthogonal polygons** (every edge
horizontal or vertical), for an explicit Turing-machine model. For general polygons the
boundary-point variant is treated by M. Abrahamsen, A. Adamaszek and T. Miltzow, *The Art Gallery
Problem is ∃ℝ-complete* (J. ACM 2021); the hardness proof for orthogonal polygons is a new
construction.

This entry complements the author's earlier Palomar entry [OAG]
(PALOMAR-2026-11-01-000004 v1, *The orthogonal art gallery problem is ∃ℝ-complete (point-point
and point-boundary), in Lean 4*), which proves the orthogonal **point-point** and
**point-boundary** variants. Those results are not restated here; this entry proves only the
boundary-point variant, by a different construction (see
[Relation to earlier entries](#relation-to-earlier-entries)).

Author and maintainer: Robert D. Barish (rbarish@ims.u-tokyo.ac.jp).

* **What Lean proves.** Deciding whether an orthogonal simple polygon with rational vertex
  coordinates can be guarded by `g` points of its boundary, which together must see every point
  of the closed polygon, is `∃ℝ`-complete under polynomial-time many-one reductions.
* **Axioms.** The proof uses exactly Lean's three standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`). There is no `sorry`, no other axiom and no `native_decide`;
  large finite computations (visibility and coverage certificates) are checked by the kernel
  (`decide +kernel`).
* **Checking.** The Lean kernel checks the proof; Comparator checks that the solution proves the
  challenge statement and replays it with the toolchain's independent kernels (see
  [Checking](#checking)). The recorded runs are local.

## The statement

The statement is [`Challenge.lean`](Challenge.lean): the definitions used by the theorem (the
machine model, ETR and `∃ℝ`, polygons, guarding, the problem), followed by one theorem in
namespace `ArtGallery`:

```lean
theorem agpOrthBoundaryPoint_erComplete : ERComplete AGPOrthBoundaryPoint
```

### Definitions

All definitions are in `Challenge.lean` with docstrings. Those that also occur in the statement of
[OAG] are unchanged. The three new ones (`IsGuardSetOnBoundary`, `HasGuardSetOnBoundaryOfCard`,
`AGPOrthBoundaryPoint`) are copied from the library's specification files
`ArtGallery/Spec.lean` and `ArtGallery/Orthogonal/Spec.lean`, which are the same as in [OAG].

* **Machines and complexity.** Deterministic single-tape Turing machines over
  {blank, 0, 1, separator}, time = number of steps, polynomial bounds `c * (n + 1)^k`,
  `PolyTime f`, `PolyRed A B` (polynomial-time many-one reductions). These are reused verbatim
  from the author's Palomar entry [NPC].
* **ETR.** Terms with constants `0, 1` and `+, −, ·`; quantifier-free formulas with `=, <, ≤`,
  `¬, ∧, ∨` over the variables `x₀, x₁, …`; `ETR` is the set of codes of satisfiable formulas.
  `InER L` means that `L` reduces to `ETR`; `ERHard L` means that every language in `∃ℝ` reduces
  to `L`; `ERComplete L` is both.
* **Codes.** Variable indices are written in unary; the numbers of an art gallery instance
  (numerators, denominators, `g`) are written in binary.
* **Polygons and guarding.** A polygon is its list of corners in boundary order; it is simple if
  it has at least three distinct corners and any two distinct edges meet exactly in their common
  endpoints (collinear consecutive corners are allowed). It is orthogonal if the two endpoints of
  every edge have equal first or equal second coordinates. Its region `filled` is the boundary
  together with the points whose component in the complement of the boundary is bounded. Two
  points see each other if the closed segment between them lies in the region. A guard set on
  the boundary is a set of boundary points such that every point of the region is seen by one of
  them. The polygon definitions are those of the author's Palomar entry [CHZ] on Chazelle's
  triangulation algorithm.
* **Problem.** `AGPOrthBoundaryPoint`: codes of a list of rational corners (numerator/denominator
  pairs) and a number `g` such that the polygon is simple, orthogonal, and has a guard set on the
  boundary with exactly `g` points (equivalently at most `g`, since the boundary is infinite and
  guards can be added).

## The proof

**Membership in `∃ℝ`.** The membership argument of [AAM] §3, in the form whose only variables
are the `2g` guard coordinates (`ArtGallery/FewVars/BoundaryPointMain.lean`), conjoined with the
variable-free test that the polygon is orthogonal (`ArtGallery/Orthogonal/Membership.lean`). Both
are taken unchanged from [OAG].

**Hardness.** The reduction is ETR → ETR-INV ([AAM] §4) → an orthogonal polygon
(`ArtGallery/Orthogonal/BoundaryPoint/`). The ETR-INV instance is compiled to rows of fourteen
relation profiles (addition, shifted and lowered addition, inversion and reversed inversion at
fixed value banks). The emitted polygon is a hub with one floor slot per variable and one door
per row; behind each door hangs an orthogonal *wing*, a staircase corridor ending in an
arithmetic room, whose boundary guards copy the slot values through the door and enforce the row
relation.

* Soundness (`ReductionSound.lean`): any guard set on the boundary of size `g` has exactly one
  guard owning each role, the owned base guards define values in `[1/2, 2]`, the copy channels
  transport them into every wing and the rooms force the row relations.
* Completeness (`Forward.lean`): the canonical guards of a satisfying assignment see the hub
  (`HubCover.lean`) and every wing in its local frame (`WingFinal/`, `WingCatalog.lean`).
* The finite visibility facts of each wing profile are kernel-checked certificates on the wing
  chart, parametric in the size and value parameters.

This construction is independent of the one of [OAG] (a modification of Stade's polygon for the
point-boundary problem): the boundary-point theorem uses only three small helper files of it.

## Checking

The project pins Lean `leanprover/lean4:v4.35.0-rc2` and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```sh
lake exe cache get
lake build
lake comparator --config comparator.json
```

The committed Lean files, including the generated certificate and data files, are the only inputs;
no source-generation step is needed. `comparator.json` enables the toolchain's NanoDa kernel in
addition to Lean's kernel (`nanoda_bin` must be on `PATH`).

Local runs (cloud container, 4 cores, 15 GB; Mathlib from the cache):

| step | wall time | peak memory |
|---|---|---|
| `lake build` from scratch, 4 cores | 5,216 s (1.45 h) | 8.0 GB (all `lean` processes) |
| `lake comparator --config comparator.json`, total (build already present) | 9,944 s (2.76 h) | 4.7 GB |
| of which NanoDa, 4 threads (accepted) | 1,758 s (0.49 h) | 4.0 GB |
| of which Lean kernel replay, one thread (accepted) | 7,931 s (2.20 h) | 2.6 GB |

`#print axioms ArtGallery.agpOrthBoundaryPoint_erComplete` reports `[propext, Classical.choice, Quot.sound]`.

## Layout

* `Challenge.lean`, `Solution.lean`, `comparator.json`: the Palomar statement, proof and
  Comparator configuration.
* `ArtGallery/Spec.lean`, `ArtGallery/Orthogonal/Spec.lean`: the definitions the statement uses
  (they also define further problems and ETR-INV, which the library uses).
* `Complexity/`, `PT/`: the machine model, a register language and a framework for proving
  polynomial time (reused from earlier entries).
* `ArtGallery/ETR/`, `ArtGallery/PTime/`: circuits, a ball theorem, the reduction
  ETR → ETR-INV and polynomial-time proofs.
* `ArtGallery/Membership/`, `ArtGallery/FewVars/`, `ArtGallery/Orthogonal/Membership*.lean`:
  membership in `∃ℝ` with `2g` variables, and the orthogonality test.
* `ArtGallery/Orthogonal/BoundaryPoint/`: the boundary-point construction: compilation of the
  source into rows, the hub and wing polygons, simplicity and orthogonality, role ownership and
  soundness, the wing and hub covers, polynomial time, and the final theorem
  (`ArtGallery/Orthogonal/BoundaryPoint/Main.lean`).
* `ArtGallery/Orthogonal/Hard/{Comb, OrthChain, RatEq}.lean`, `ArtGallery/Stade/`: helper
  lemmas from [OAG].
* `ArtGallery/Vis/`, `ArtGallery/{Geometry, Jordan, Existence, Invariance, Irrational}/`:
  visibility in polygons, planar geometry, the Jordan curve theorem for polygons, triangulations,
  affine invariance and certificate checkers.

## Relation to earlier entries

* **[OAG]** (PALOMAR-2026-11-01-000004 v1) proves that the orthogonal point-point and
  point-boundary art gallery problems are `∃ℝ`-complete, and that both reduce to ETR by formulas
  in the `2g` guard coordinates. This entry is its companion for the third variant,
  boundary-point. Its statement uses the same definitions as [OAG] (`AGPOrthBoundaryPoint`
  differs from `AGPOrth` only in requiring the guards to lie on the boundary).
* **Shared files.** The proof consists of 1,819 Lean files (besides `Challenge.lean` and
  `Solution.lean`). The 1,676 files of `ArtGallery/Orthogonal/BoundaryPoint/` are new. The other
  143 files are byte-identical copies of the files of the same path in [OAG]: the definitions
  (`ArtGallery/Spec.lean`, `ArtGallery/Orthogonal/Spec.lean`), the membership argument and the
  orthogonality test, three helper files of its construction
  (`ArtGallery/Orthogonal/Hard/{Comb, OrthChain, RatEq}.lean`), and the libraries listed below.
  Their origins are recorded file by file in [OAG]'s `docs/PROVENANCE.md`.
* **Earlier origins.** Through [OAG], the ETR reductions, the membership argument and the geometry
  and visibility library come from the author's entry [AGP] (PALOMAR-2026-10-27-000025 v1); the
  machine model, the polynomial-time framework and part of the complexity library come from
  [NPC] and [MAX]; the polygon definitions and the planar-geometry and Jordan-curve library are
  adapted from [CHZ], and each adapted file carries a provenance note in its header.

AI assistance is acknowledged: Claude Opus 5.5 (Anthropic) was used for the Lean formalization
and to assist with the documentation. The generated Lean files (certificates and construction
data) were produced by development programs (exact rational arithmetic) that are not part of this
repository; all generated files are checked by the Lean kernel like all other files. See
`formalization.yaml` for the automation and review metadata.

Development date: 2026-11-08.

## References

* [AAM] M. Abrahamsen, A. Adamaszek, T. Miltzow. The art gallery problem is ∃ℝ-complete.
  Journal of the ACM 69(1), Article 4 (2021). Preliminary version STOC 2018.
* [OAG] R. D. Barish. The orthogonal art gallery problem is ∃ℝ-complete (point-point and
  point-boundary), in Lean 4. Palomar, PALOMAR-2026-11-01-000004 v1 (2026).
  <https://palomar-registry.org/entry?id=PALOMAR-2026-11-01-000004&version=1>
* [AGP] R. D. Barish. The Art Gallery Problem is ∃ℝ-complete: point-point, boundary-point and
  point-boundary variants, in Lean 4. Palomar, PALOMAR-2026-10-27-000025 v1 (2026).
  <https://palomar-registry.org/entry?id=PALOMAR-2026-10-27-000025&version=1>
* [NPC] R. D. Barish. NP-completeness of SAT, 3-SAT and their variants (the Cook–Levin theorem)
  in Lean 4. Palomar, PALOMAR-2026-10-02-000013 v1 (2026).
  <https://palomar-registry.org/entry?id=PALOMAR-2026-10-02-000013&version=1>
* [MAX] R. D. Barish. MaxSNP-completeness and APX-completeness of MAX-3-SAT and 3-OCCURRENCE
  MAX-3-SAT (the PCP theorem and hardness of approximation) in Lean 4. Palomar,
  PALOMAR-2026-10-09-000010 v1 (2026).
  <https://palomar-registry.org/entry?id=PALOMAR-2026-10-09-000010&version=1>
* [CHZ] R. D. Barish. Linear-Time Triangulation of Simple Polygons (Chazelle's Algorithm) in
  Lean 4. Palomar, PALOMAR-2026-10-05-000003 v2 (2026).
  <https://palomar-registry.org/entry?id=PALOMAR-2026-10-05-000003&version=2>

## License

Apache License 2.0 ([`LICENSE`](LICENSE)). Mathlib and its dependencies retain their own
licenses.
