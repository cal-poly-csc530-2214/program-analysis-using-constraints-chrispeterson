# Assignment 4: Program Analysis w/ Constraints by Christopher Peterson

## What I did


## Calculation by hand

Before coding anything, I always like to work through the process by hand. For this paper, this process turned out to be pretty challenging and not trivial at all.

My goal was to validate the example given by the authors (shown below) using the template ``a1x + a2y + a3 ≥ 0 ∨ a4x + a5y + a6 ≥ 0`` for ``I``.

```
true => I[-50/x]
I ^ x < 0 => I[(y + 1)/y, (x + y) / x]
I ^ x >= 0 => y > 0
```

### Statement 1

``true => I[-50/x]`` becomes ``true => -50a1 + a2y + a3 ≥ 0 ∨ -50a4 + a5y + a6 ≥ 0`` by substitution.

More substituion to begin preparing for Farkas' lemma:
```
e1 = -50a1 + a2y + a3
e2 = -50a4 + a5y + a6

true => e1 >= 0 V e2 >= 0
```

Each piece of the conjunction can be negated using the hacky ints-only trick described in lecture. The intuition here is that the original statements are true if ``e`` is between ``[0, positive_infinity)``, which remains the case after the negation, subtraction, and not are added:
```
e1 >= 0 becomes !(-e1 - 1 >= 0)
e2 >= 0 becomes !(-e2 - 1 >= 0)

resulting in:
true => !(-e1 - 1 >= 0) V !(-e2 - 1 >= 0)
```

Applying De'Morgan's law so that Farkas' lemma will work:
```
true => !((-e1 - 1 >= 0) ^ !(-e2 - 1 >= 0))
```

Applying Farkas' lemma. I don't fully understand where/when exactly the quantifier ``∀x,y`` comes in to allow for the lemma usage, but it seems to have been implied throughout all the previous calculations (since these statements for I must hold for all values of ``x`` and ``y``, otherwise they wouldn't be very useful):
```
∃λ > 0, λ1,λ2 >= 0(∀x,y λ1(−e1 − 1) + λ2(−e2 − 1) = −λ)
```

Looking at the inner statement more closely:
```
∀x,y λ1(−e1 − 1) + λ2(−e2 − 1) = −λ
e1 = -50a1 + a2y + a3
e2 = -50a4 + a5y + a6

∀x,y λ1(50a1 - a2y - a3 − 1) + λ2(50a4 - a5y - a6 − 1) = −λ
∀x,y 50a1λ1 - a2yλ1 - a3λ1 − λ1 + 50a4λ2 - a5yλ2 - a6λ2 − λ2 = −λ
```
