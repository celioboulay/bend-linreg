# bend-linreg

In case you didn't trust scikit-learn, here is linear regression in
[Bend](https://bend-lang.com): exact fractions, no rounding, and laws for the
code to prove.

**Try it:** https://celioboulay.github.io/bend-linreg/

| File | What it holds |
|---|---|
| `num.bend` | `Int` and `Rat`, always in lowest terms |
| `linreg.bend` | `LinearRegression.fit / predict / score`, one feature |
| `LAWS.bend` | the laws: least squares, normal equations, errors, arithmetic |
| `web/` | the page; `web/build.sh` rebuilds `docs/index.html` |

**Limitation:** Bend's runtime stops on numbers above 2^48 − 1, so `fit`,
`predict` and `score` return `TooLarge` when an exact result could get that
big. With whole numbers, `fit` accepts values up to about 412 for 1,000 points.
