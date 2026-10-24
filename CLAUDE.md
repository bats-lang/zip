# zip

## CI is pinned

Every input to CI is pinned in the source (bats-lang/repository-prototype#269),
so a commit that passes keeps passing:

* `bats.lock` is committed: CI never runs `bats lock` for the package, so
  `bats check` and `bats build` fetch exactly the locked versions, and fail
  when the lock is missing or does not match `bats.toml`. A library's lock
  pins only its own CI and tests; its dependents still resolve their own.
* The compiler is the commit in `.github/bats-version`, read by every
  workflow that builds bats (and by the publish workflow).
* The package repository is fetched at the commit in
  `.github/repository-version`, so what the test packages under `tests/`
  lock (`bats lock --dev`) is pinned too.
* `publish.yml` and `relock-pins.yml` in bats-lang/repository-prototype are
  called by commit, never `@main`.

Pins move only through a reviewed pull request that runs the same CI. The
daily `relock.yml` (the shared `relock-pins.yml`) relocks against the
newest, moves the compiler and repository pins, pushes `relock/<date>`,
opens a pull request listing the old and new versions and dispatches
`check.yml` on it, so a breaking publish shows as a red relock pull
request and main stays green. GITHUB_TOKEN cannot change workflow files,
so without a `RELOCK_TOKEN` secret that pull request lists a workflow pin
that would move instead of moving it: move it in a pull request of its
own. A pull request that needs newer packages runs `bats lock
--repository <dir>` and commits `bats.lock` (and
`.github/repository-version`) with the change.

## INFLATES: what inflating an entry's data gives, as a relation (bats-lang/quire#608)

`INFLATES(kind, compressed, output)` says that an entry's data, whose array
cells are `compressed` (array's `cells`), inflates by the method `kind`
(`inflate_stored`, `inflate_deflated`, the static form of `compression`) to
the cells `output`. `inflates_functional` is its lemma: the same method and
compressed cells give the same output cells, concluded as `CELLS_EQ`.

Only the stored method (ZIP method 0, bytes kept as they are) has a
constructor so far. The Deflated method is RFC 1951 and is added by the
pieces that follow in quire#608 (zip#64 to #71), constructor by constructor,
each extending `inflates_functional`. This piece adds new names only: no
published signature changed. Proved, not tested: the relation is a
specification, so there is nothing to run; `tests/static/accept/inflates-stored-use`
uses it and `tests/static/reject/inflates-*` reject a stored entry inflating
to other cells or claimed deflated, and the lemma used for other compressed
cells, another method, or to conclude the outputs differ. The lemma's two
mutants (`tests/static/mutation_check.py` of quire, over `src/lib.bats`, the
GMP solver) are both rejected.
