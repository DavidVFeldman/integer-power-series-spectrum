# Release recipe (run in this order)

1. Push this tree to `main`; confirm the Actions run is green (both the
   build and the axiom audit steps).
2. On zenodo.org, log in with GitHub and flip the toggle for
   `integer-power-series-spectrum` ON. **Before** any release — Zenodo
   only captures releases made after the toggle.
3. GitHub -> Releases -> Create a new release. Tag `v1.0`, title `v1.0`.
   Paste the description below. Publish. Zenodo mints the DOI within
   minutes; note both the concept DOI and the version DOI.
4. Fill the concept DOI into: the README DOI badge (add under the CI
   badge), CITATION.cff (`doi:` field), and the paper's bibliography as
   a `\cite{Repo}` entry if desired. Bump CITATION.cff `version: "1.1"`.
5. Commit, push, cut `v1.1`. The concept DOI now resolves to v1.1.
6. On the Zenodo record: confirm authors display as "Bannon, Jon" and
   "Feldman, David Victor" with ORCID (not the GitHub handle); add the
   arXiv ID as a related identifier once assigned.

## Release description for v1.0

Two companion papers with complete Lean 4 formalization: the realization
of conjugation-invariant divisors on the unit disk by integer-coefficient
holomorphic functions (Paper I), and the prime and maximal spectra of
Z[[z]] cap O(D) (Paper II), including the p-adic evaluation primes Q_p
with quotient Z_p. Every numbered result of both papers is
machine-verified (propext, Classical.choice, Quot.sound only). This
release includes the machine-checked refutation
(`primes_outside_classification_false`) of a classification the authors
themselves briefly believed.
