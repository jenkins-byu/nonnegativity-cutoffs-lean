# Palomar submission preparation

## Repository status

This is the substantive formalization repository, published on the `main` branch as
[`jenkins-byu/nonnegativity-cutoffs-lean`](https://github.com/jenkins-byu/nonnegativity-cutoffs-lean).
An earlier snapshot was submitted to Palomar. Its protected Lean verification passed, but the
post-verification renderability stage did not complete because Palomar's dispatch infrastructure
failed. The present Lean 4.35 compatibility update has not yet been published or resubmitted.

The intended Palomar comparison consists of:

- `Challenge.lean`, the short Mathlib-only statement surface;
- `Solution.lean`, the corresponding proved declaration;
- `comparator.json`, selecting
`NonnegativeModularForms.exists_optimal_nonnegativity_cutoff`; and
- `formalization.yaml`, recording authorship, provenance, scope, automation, fidelity, and review.

## Mathematical statement

For each natural-number weight `k` satisfying `12 ≤ k` and `k % 4 = 0`, the compared theorem
produces a positive natural number `A` and proves three claims about level-one modular forms with
real q-expansion coefficients:

1. nonnegativity of the coefficients at every index `n ≤ A`, including `n = 0`, implies
   nonnegativity at every index;
2. some such modular form has its first negative coefficient exactly at `A`; and
3. every first negative coefficient index of every such form is at most `A`.

The last two claims say that `A` is the greatest attainable first negative index. This is the
paper's maximum characterization of `A(k)`, while the first claim is its inclusive finite-test
interpretation.

## Source correspondence

The primary source is Paul Jenkins and Jeremy Rouse, *Modular Forms with Only Nonnegative
Coefficients*, *Research in Number Theory* **12**, article 56 (2026),
<https://doi.org/10.1007/s40993-026-00744-z>.

The formalization covers the qualitative level-one well-definedness argument from Section 4. The
full production development includes the normalized bounded finite convex-polytope and finite
coefficient-determination statements. The compared Palomar theorem is a streamlined consequence:
it directly records finite detection and the greatest-first-negative-index characterization.

The compared theorem deliberately omits:

- the low-weight conventions `A(4) = A(8) = 1`;
- numerical values of `A(k)`;
- the explicit estimates in Sections 5 and 6; and
- all higher-level analogues.

## Authorship, maintenance, and automation

Paul Jenkins is the formalization author and responsible maintainer. Jeremy Rouse is a coauthor of
the mathematical source; this draft does not claim that he reviewed or endorsed the Lean
development.

OpenAI Codex was used substantially for Lean development, API investigation, proof repair,
documentation, and verification under human mathematical direction. It is disclosed as
automation and is not an author. The exact underlying model identifier was not recorded in the
project metadata.

## Author review completed

The maintainer has audited `Challenge.lean` and confirmed:

- `ModularForm 𝒮ℒ (k : ℤ)` has the intended level-one and weight conventions;
- the zero-imaginary-part hypothesis exactly expresses real Fourier coefficients;
- the cutoff is inclusive and intentionally includes the constant coefficient;
- the first-negative-index clauses use strict inequality at the chosen index and nonnegativity at
  every earlier index;
- the weight assumptions `12 ≤ k` and `k % 4 = 0` match the intended submitted scope;
- the combination of attainment and upper boundedness accurately expresses “greatest”; and
- the fidelity and automation descriptions in `formalization.yaml` are complete.

External mathematical or Lean review may be added later. Until then, `formalization.yaml`
accurately records the review status as author-verified without claiming a separate reviewer.

## Final local verification

The Lean 4.35 compatibility update completed the final verification available on this Windows
host. On 2026-09-24, the local compiled outputs were removed with `lake.ps1 clean` and every
default target was rebuilt from the
pinned source and dependency graph. The cold build completed successfully with 3,507 jobs. Its
only `sorry` warning came from the one deliberate placeholder in `Challenge.lean`; the production
development, `Section4.NonnegativityBound`, the aggregate `Section4` target, and `Solution.lean`
all compiled without proof-hole warnings.

The independent post-build checks confirmed:

- a recursive scan of the project Lean sources found exactly one `sorry`, at `Challenge.lean:51`,
  and no `admit`, `native_decide`, `Lean.ofReduceBool`, custom `axiom`, or `unsafe` declaration;
- `#print axioms NonnegativeModularForms.exists_optimal_nonnegativity_cutoff` reported exactly
  `propext`, `Classical.choice`, and `Quot.sound`;
- `comparator.json` parses and selects the intended Challenge, Solution, and theorem, with those
  three permitted axioms and NanoDa enabled; and
- `formalization.yaml` passed the current official v0.4 schema again on 2026-09-21.

The protected Palomar verification was not simulated locally and is not claimed here. This host
has no installed Comparator, `lean4export`, NanoDa, or Landrun binaries, no Rust or Go toolchain
with which to build them, and neither WSL nor Docker. Comparator documents a fake-Landrun
development mode for non-Linux systems, but that would not reproduce Palomar's Linux Landlock
boundary.

After publication, the clean GitHub-hosted Linux build passed both on the initial push and in the
[manually dispatched Task 8 run](https://github.com/jenkins-byu/nonnegativity-cutoffs-lean/actions/runs/35776538664).
That run also successfully resolved Palomar's approved execution profile, but its protected
verification job could not start because the selected Namespace-managed runner was unavailable
to the calling repository. The predictive preflight is therefore not claimed. It is advisory
rather than a registry submission; the authoritative protected Comparator/NanoDa/Landrun checks
remain to be performed by Palomar's submission verification.

## Submission-readiness audit

The local Task 5 audit completed on 2026-09-18 against the current published Palomar submission
requirements. It confirmed:

- the conventional repository-root layout, with exactly one `lakefile.toml`, one root `LICENSE`,
  a `lake-manifest.json` ready for the initial commit, and the expected Challenge, Solution,
  Comparator, and metadata files;
- Lean `v4.35.0-rc2`, exactly matching the toolchain of the pinned Mathlib revision;
- public GitHub dependency URLs and full lowercase 40-character revisions for all nine Git
  packages, with the flattened manifest agreeing with Mathlib's own dependency pins;
- a 51-line, 2,655-byte Challenge whose source dependency closure contains only Lean core and
  the pinned Mathlib statement surface;
- identical normalized theorem types in `Challenge.lean` and `Solution.lean`, exactly one
  intentional Challenge `sorry`, no proof holes or forbidden axiom declarations elsewhere in
  the project Lean sources, and precisely `propext`, `Classical.choice`, and `Quot.sound` in the
  proved theorem's axiom report;
- valid Comparator JSON and `formalization.yaml` v0.4 metadata, including checked Palomar
  taxonomy entries `math.NT`, `11F11`, and `11F30`;
- consistent Apache-2.0 repository and metadata licensing;
- a 39-file public source snapshot, with valid UTF-8 text, no symbolic links,
  Git LFS pointers, submodules, compiled artifacts, private local paths, email addresses, or
  secret-like credentials; and
- a valid read-only GitHub Actions build workflow whose third-party actions are pinned to full
  commit revisions.

Task 6 supplied the final local verification described above. Task 7 published the initial source
snapshot. Task 8 confirmed the clean public Linux build and attempted the predictive Palomar
preflight; the profile stage passed, but the protected verification job could not obtain its
external runner. The authoritative Palomar Comparator/NanoDa/Landrun checks therefore remain for
submission verification.
