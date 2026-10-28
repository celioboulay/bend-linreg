# bend-linreg

Exact least-squares linear regression in [Bend](https://bend-lang.com), on
rational numbers, so there is no rounding anywhere.

**Try it:** https://celioboulay.github.io/bend-linreg/ runs this code,
compiled to JavaScript, in the browser.

## Files

| File | What it holds |
|---|---|
| `num.bend` | `Int` and `Rat` (always in lowest terms), gcd |
| `linreg.bend` | `LinearRegression.fit / predict / score`, one feature, sklearn-style |
| `LAWS.bend` | the laws the code must satisfy (least squares, normal equations, errors, arithmetic) |
| `web/` | the page source; `web/build.sh` rebuilds `docs/index.html` |

## Use

```sh
bend linreg.bend --check-only   # type-check
bend LAWS.bend                  # lists the laws still to prove
./web/build.sh                  # rebuild the web page after changing linreg.bend
```

## Status

- **Phase A (one feature):** implemented and tested against Python's `fractions`.
- **Proofs:** the laws in `LAWS.bend` are stated but not proven yet, so
  `bend LAWS.bend` reports them as open.
- **Phase B (several features):** not started.

## Limitation

Bend's runtime stops on any natural number above 2^48 − 1. Before computing,
`fit`, `predict` and `score` check that nothing they compute can exceed
2^47, and return `TooLarge` otherwise. For `fit` the condition is

    n² · B² · max(2B, L) ≤ 2^47

with `n` points, `L` the lcm of all denominators and `B` the largest |x·L| or
|y·L|. With whole numbers, that allows values up to about 26,000 for 2 points,
about 412 for 1,000 points and about 19 for 100,000 points. The conditions for
`predict` and `score` are at the top of `linreg.bend`.
