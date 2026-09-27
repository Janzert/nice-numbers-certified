# nice-numbers-certified

Machine-checked statements that a particular base has **no** nice number.

A number `n` is **nice in base `b`** when the base-`b` digits of `n^2` and `n^3` together use
every digit `0 … b-1` exactly once. The only one known is 69 in base 10 (`69^2 = 4761`,
`69^3 = 328509`). More generally `n` is **`(e1,e2)`-nice** when `n^e1` and `n^e2` share the
digits out that way.

The theorems for all bases are in
[nice-numbers-lean](https://github.com/Janzert/nice-numbers-lean), and this project depends
on it. Each result here is stated with that project's `Pandigital`, so "no nice number in
base 17" means exactly what it means there. Proofs are in Lean 4 core, with no Mathlib, no
`sorry` and no `native_decide`.

## What is proved

**`Nice.Cert.two_three_upto_20`:** for every base `2 ≤ b ≤ 20`, `n` is `(2,3)`-nice in
base `b` if and only if `b = 10` and `n = 69`.

Base 10 comes from nice-numbers-lean (`Nice.base_ten_nice_iff`). Every other base has a
theorem `Nice.Cert.base_<b>_empty_2_3` saying it has no `(2,3)`-nice number, in
`NiceCertified/TwoThree/Base<b>.lean`, built from the parts in `NiceCertified/TwoThree/Base<b>/`.
The work each base takes, counted as nodes of the search tree plus candidates checked one
by one:

| base | parts | nodes + candidates |
|---|---|---|
| 2 | 1 | 1 |
| 3 | 0 | 0 |
| 4 | 1 | 2 |
| 5 | 1 | 3 |
| 6 | 1 | 2 |
| 7 | 1 | 9 |
| 8 | 1 | 10 |
| 9 | 1 | 15 |
| 11 | 1 | 2 |
| 12 | 1 | 172 |
| 13 | 1 | 236 |
| 14 | 1 | 444 |
| 15 | 1 | 2 019 |
| 16 | 1 | 2 |
| 17 | 3 | 6 361 |
| 18 | 4 | 8 377 |
| 19 | 7 | 16 346 |
| 20 | 36 | 82 274 |

Base 3 has no candidates at all. Some other bases are also ruled out by general theorems in
nice-numbers-lean: `b ≡ 1 (mod 5)` makes the digit lengths impossible (bases 6, 11, 16), and
`b ≡ 3 (mod 4)` rules out the digit sum (bases 7, 11, 15, 19). Each base is proved here
directly anyway, so every row stands on the same checker.

## How it works

[`NiceCertified/Checker.lean`](NiceCertified/Checker.lean) defines a checker and proves it
sound once, for every base. It covers every `n` whose powers could have `b` digits between
them with consecutive intervals, and gives each one a reason nothing in it is nice:

- **wrong lengths:** across the interval, the digit counts of `n^e1` and `n^e2` are
  constant and do not add up to `b`;
- **top-digit clash:** the leading digits of both powers are the same for every `n` in the
  interval, and they already repeat a digit. Two endpoints rule out the whole interval;
- **scanned:** every `n` in the interval is checked in full.

The intervals are not listed. The kernel builds them itself (`refute`): at each interval it
tries a top-digit clash, scans the interval if it is narrow enough, and otherwise splits it
at multiples of a power of `b` and recurses. `refute_sound` proves that search sound, so a
base costs nothing but evaluation: each part is one `decide +kernel` on a range of `n`.

[`gen/gen.py`](gen/gen.py) (Python standard library only) chooses those ranges. It walks the
same search the kernel will walk, to split the band into parts of bounded work. Nothing
about the generator needs to be trusted: a wrong range fails the kernel check. For example,
the parts it writes for base 10 are rejected, because 69 is in the band.

## Checking it

```bash
lake build
```

This fetches nice-numbers-lean at the revision pinned in
[`lakefile.toml`](lakefile.toml) and builds both projects. At the end it prints
`#print axioms` for each theorem, which should list only `propext`, `Classical.choice` and
`Quot.sound`. The `lean-toolchain` file selects Lean v4.33.0.

**Memory.** The kernel keeps what it reduces for the life of the Lean process, and does not
give it back between declarations in one file. That costs roughly half a megabyte per tree
node or checked candidate, so base 20 checked as one declaration would need tens of
gigabytes. So each part is its own module, bounded at about 2 500 units, which is about
1.7 GB. Each part imports the one before it, and each base's first part imports the previous
base, so the whole build is one chain and Lake checks one part at a time. A full build takes
a few minutes and should peak under 2 GB.

To regenerate every base's modules:

```bash
python3 gen/gen.py --range 2 20 2 3 20 --budget 2500 --skip 10
```

The arguments are the range of bases, the exponent pair and the widest interval scanned
instead of split. `--budget` is the work per part, and `--skip` lists bases proved elsewhere.

## Licence

MIT, as for nice-numbers-lean.
