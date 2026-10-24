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
cells, another method, or to conclude the outputs differ. The lemma is
mutation-checked (next section).

## The lemmas are mutation-checked under the infinite-precision solver (bats-lang/quire#594)

The 32-bit solver can make a proof's context contradictory, so a lemma proves
nothing while every other check is green. Every lemma of `src/lib.bats` (today
`inflates_functional`; `CELLS_EQ` and `INFLATES` are dataprops, `prval ... fold@`
is not a lemma) is checked with false variants of its statement, which the
compiler must reject: quire's `tests/static/mutation_check.py`, from a clone of
bats-lang/quire, with the GMP build of ATS2 as `--ats-home` (CI's solver: the
bats setup action runs `bats ats2 install`). Every control is accepted and every
mutant rejected. An accepted mutant is a vacuous lemma (file it as a p1) or an
equivalent mutant listed with its reason in `tests/static/mutation_known.txt`;
a lemma concluding `[false] void` has no false variant and gets a reject fixture
in `tests/static/reject` instead (run by `tests/static/run.sh` in CI). A new
lemma, or a new constructor of `INFLATES` that changes the lemma's body (zip#64
to #71), is run through the checker again:

```
BATS_CHECK="bats check --repository REPO" python3 -B -I quire/tests/static/mutation_check.py \
  --root . --run WORK --ats-home GMP_HOME/.bats/ats2 --inplace \
  --known tests/static/mutation_known.txt src/lib.bats
```

`WORK` is a copy of the checkout that `bats check` has already passed (its
`build/` kept); the checkout itself is not written.
