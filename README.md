# Assignment 4: Program Analysis w/ Constraints by Christopher Peterson

## What I did


## Calculation by hand

Before coding anything, I always like to work through the process by hand. For this paper, this process turned out to be pretty challenging and not trivial at all.

My goal was to validate the example given by the authors (shown below) using the template ``a1x + a2y + a3 >= 0 ∨ a4x + a5y + a6 >= 0`` for ``I``.

```
true => I[-50/x]
I ^ x < 0 => I[(y + 1)/y, (x + y) / x]
I ^ x >= 0 => y > 0
```

### Statement 1

``true => I[-50/x]`` becomes ``true => -50a1 + a2y + a3 >= 0 V -50a4 + a5y + a6 >= 0`` by substitution.

More substituion to begin preparing for Farkas' lemma:
```
e1 = -50a1 + a2y + a3
e2 = -50a4 + a5y + a6

true => e1 >= 0 V e2 >= 0

changing implies into a not and an or:
false V e1 >= 0 V e2 >= 0

false or gets dropped off:
e1 >= 0 V e2 >= 0
```

Each piece of the conjunction can be negated using the hacky ints-only trick described in lecture. The intuition here is that the original statements are true if ``e`` is between ``[0, positive_infinity)``, which remains the case after the negation, subtraction, and not are added:
```
e1 >= 0 becomes !(-e1 - 1 >= 0)
e2 >= 0 becomes !(-e2 - 1 >= 0)

resulting in:
!(-e1 - 1 >= 0) V !(-e2 - 1 >= 0)
```

Applying De'Morgan's law so that Farkas' lemma will work:
```
!((-e1 - 1 >= 0) ^ (-e2 - 1 >= 0))
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

I tried to come up with a generalized way to simplify these statements using z3 but was totally unsuccessful. I don't know if this was due to a lack of my understanding or it just not being what z3 is designed for.

The method that the authors use in the paper is simple enough for this example, although I'm not entirely sure how it will work for pieces with mixed ``x``'s and ``y``'s. In order for the statement to be true regardless of x and y values, it must be constructed in such a way that the ``x``'s and ``y``'s cancel out. This is seemingly done in a pretty simple process of splitting out the terms with each type of variable in them, removing the variable, and setting it equal to 0 (taking advantage of the fact that they're all coefficients):
```
∀x,y 50a1λ1 - a2yλ1 - a3λ1 − λ1 + 50a4λ2 - a5yλ2 - a6λ2 − λ2 = −λ

terms with x: None
resulting expression: N/A

terms with y: - a2yλ1 - a5yλ2
resulting expression: -a2λ1 - a5λ2 = 0

terms without x or y: 50a1λ1 - a3λ1 − λ1 + 50a4λ2 - a6λ2 − λ2 = −λ
```

This results in a final expression (I think?) of:
```
∃λ > 0, λ1,λ2 >= 0 ((-a2λ1 - a5λ2 = 0) ^ (50a1λ1 - a3λ1 − λ1 + 50a4λ2 - a6λ2 − λ2 = −λ))
```

If my understanding is correct; this result will be and'd with the results from the other steps to get a satisfiability equation that will give values for the a's.

### Statement 2

Statement 2 is immediately a lot more tricky because it has a lot more going on (and the authors do not provide a step-by-step walkthrough), but I'll try to follow the same process:

``I ^ x < 0 => I[(y + 1)/y, (x + y)/x]`` becomes ``(a1x + a2y + a3 >= 0 ∨ a4x + a5y + a6 >= 0) ^ (x < 0) => a1(x + y) + a2(y + 1) + a3 >= 0 ∨ a4(x + y) + a5(y + 1) + a6 >= 0`` by substitution.

More substituion to begin preparing for Farkas' lemma:
```
e1 = a1x + a2y + a3
e2 = a4x + a5y + a6
e3 = -x - 1
e4 = a1(x + y) + a2(y + 1) + a3
e5 = a4(x + y) + a5(y + 1) + a6

(e1 >= 0 V e2 >= 0) ^ (e3 >= 0) => e4 >= 0 V e5 >= 0

changing implies into a not and an or:
!((e1 >= 0 V e2 >= 0) ^ (e3 >= 0)) V e4 >= 0 V e5 >= 0
```

De'morgan's law twice:
```
!((e1 >= 0 V e2 >= 0) ^ (e3 >= 0)) V e4 >= 0 V e5 >= 0

becomes:
!(e1 >= 0 V e2 >= 0) V !(e3 >= 0) V e4 >= 0 V e5 >= 0

which becomes:
(!(e1 >= 0) ^ !(e2 >= 0)) V !(e3 >= 0) V e4 >= 0 V e5 >= 0
```

Distributing the and in order to get to CNF:
```
(!(e1 >= 0) V !(e3 >= 0) V e4 >= 0 V e5 >= 0) ^ (!(e2 >= 0) V !(e3 >= 0) V e4 >= 0 V e5 >= 0)
```

Double negation in order to do De'Morgan's again to be in form required by Farkas' lemma:
```
!!(!(e1 >= 0) V !(e3 >= 0) V e4 >= 0 V e5 >= 0) ^ !!(!(e2 >= 0) V !(e3 >= 0) V e4 >= 0 V e5 >= 0)

De'Morgan's:
!(e1 >= 0 ^ e3 >= 0 ^ !(e4 >= 0) ^ !(e5 >= 0)) ^ !(e2 >= 0 ^ e3 >= 0 ^ !(e4 >= 0) ^ !(e5 >= 0))
```

Doing the same trick as before in order to make each piece into non-negated expression appropriate for Farkas' lemma:
```
e4 >= 0 becomes !(-e4 - 1 >= 0)
etc...

resulting in:
!(e1 >= 0 ^ e3 >= 0 ^ (-e4 - 1 >= 0) ^ (-e5 - 1 >= 0)) ^ !(e2 >= 0 ^ e3 >= 0 ^ (-e4 - 1 >= 0) ^ (-e5 - 1 >= 0))
```

Applying Farkas' lemma to each part. The (previously implied, now shown) universal quantifier can be pushed down into the and statement, allowing this.
```
∀x,y !(e1 >= 0 ^ e3 >= 0 ^ (-e4 - 1 >= 0) ^ (-e5 - 1 >= 0)) ^ !(e2 >= 0 ^ e3 >= 0 ^ (-e4 - 1 >= 0) ^ (-e5 - 1 >= 0))

pushing down the quantifier, since it's universal with an and this doesn't change the meaning:
(∀x,y !(e1 >= 0 ^ e3 >= 0 ^ (-e4 - 1 >= 0) ^ (-e5 - 1 >= 0))) ^ (∀x,y !(e2 >= 0 ^ e3 >= 0 ^ (-e4 - 1 >= 0) ^ (-e5 - 1 >= 0)))

Farkas' lemma:
(∃λ > 0, λ1,λ3,λ4,λ5 >= 0(∀x,y λ1e1 + λ3e3 + λ4(-e4 - 1) + λ5(-e5 - 1) = −λ)) ^ (∃λ > 0, λ2,λ3,λ4,λ5 >= 0(∀x,y λ2e2 + λ3e3 + λ4(-e4 - 1) + λ5(-e5 - 1) = −λ))
```

Looking at the inner part of the first term:
```
λ1e1 + λ3e3 + λ4(-e4 - 1) + λ5(-e5 - 1) = −λ

e1 = a1x + a2y + a3
e2 = a4x + a5y + a6
e3 = -x - 1
e4 = a1(x + y) + a2(y + 1) + a3
e5 = a4(x + y) + a5(y + 1) + a6

putting the e's back in:
λ1(a1x + a2y + a3) + λ3(-x - 1) + λ4(-a1(x + y) - a2(y + 1) - a3 - 1) + λ5(-a4(x + y) - a5(y + 1) - a6 - 1) = −λ

not distributing the λis, as that'd just make it more complicated:
λ1(a1x + a2y + a3) + λ3(-x - 1) + λ4(-a1x - a1y - a2y - a2 - a3 - 1) + λ5(-a4x - a4y - a5y - a5 - a6 - 1) = −λ
```

Same process as before:
```
∀x,y λ1(a1x + a2y + a3) + λ3(-x - 1) + λ4(-a1x - a1y - a2y - a2 - a3 - 1) + λ5(-a4x - a4y - a5y - a5 - a6 - 1) = −λ

terms with x: λ1a1x - λ3x - λ4a1x - λ5a4x
resulting expression: λ1a1 - λ3 - λ4a1 - λ5a4 = 0

terms with y: λ1a2y - λ4a1y - λ4a2y - λ5a4y - λ5a5y
resulting expression: λ1a2 - λ4a1 - λ4a2 - λ5a4 - λ5a5 = 0

terms without x or y: λ1a3 - λ3 + λ4(-a2 - a3 - 1) + λ5(-a5 - a6 - 1) = −λ

final expression (I think?):
∃λ > 0, λ1,λ3,λ4,λ5 >= 0 ((λ1a1 - λ3 - λ4a1 - λ5a4 = 0) ^ (λ1a2 - λ4a1 - λ4a2 - λ5a4 - λ5a5 = 0) ^ (λ1a3 - λ3 + λ4(-a2 - a3 - 1) + λ5(-a5 - a6 - 1) = −λ))
```

Looking at the inner part of the second term:
```
λ2e2 + λ3e3 + λ4(-e4 - 1) + λ5(-e5 - 1) = −λ

e1 = a1x + a2y + a3
e2 = a4x + a5y + a6
e3 = -x - 1
e4 = a1(x + y) + a2(y + 1) + a3
e5 = a4(x + y) + a5(y + 1) + a6

putting the e's back in:
λ2(a4x + a5y + a6) + λ3(-x - 1) + λ4(-a1(x + y) - a2(y + 1) - a3 - 1) + λ5(-a4(x + y) - a5(y + 1) - a6 - 1) = −λ

not distributing the λis, as that'd just make it more complicated:
λ2(a4x + a5y + a6) + λ3(-x - 1) + λ4(-a1x - a1y - a2y - a2 - a3 - 1) + λ5(-a4x - a4y - a5y - a5 - a6 - 1) = −λ
```

Same process as before (again):
```
∀x,y λ2(a4x + a5y + a6) + λ3(-x - 1) + λ4(-a1x - a1y - a2y - a2 - a3 - 1) + λ5(-a4x - a4y - a5y - a5 - a6 - 1) = −λ

terms with x: λ2a4x - λ3x - λ4a1x - λ5a4x
resulting expression: λ2a4 - λ3 - λ4a1 - λ5a4 = 0

terms with y: λ2a5y - λ4a1y - λ4a2y - λ5a4y - λ5a5y
resulting expression: λ2a5 - λ4a1 - λ4a2 - λ5a4 - λ5a5 = 0

terms without x or y: λ2a6 - λ3 + λ4(-a2 - a3 - 1) + λ5(-a5 - a6 - 1) = −λ

final expression (I think?):
∃λ > 0, λ2,λ3,λ4,λ5 >= 0 ((λ2a4 - λ3 - λ4a1 - λ5a4 = 0) ^ (λ2a5 - λ4a1 - λ4a2 - λ5a4 - λ5a5 = 0) ^ (λ2a6 - λ3 + λ4(-a2 - a3 - 1) + λ5(-a5 - a6 - 1) = −λ))
```

Taking the two expressions together places additional constraints on the a values:
```
∃λ > 0, λ1,λ3,λ4,λ5 >= 0 ((λ1a1 - λ3 - λ4a1 - λ5a4 = 0) ^ (λ1a2 - λ4a1 - λ4a2 - λ5a4 - λ5a5 = 0) ^ (λ1a3 - λ3 + λ4(-a2 - a3 - 1) + λ5(-a5 - a6 - 1) = −λ))
and
∃λ > 0, λ2,λ3,λ4,λ5 >= 0 ((λ2a4 - λ3 - λ4a1 - λ5a4 = 0) ^ (λ2a5 - λ4a1 - λ4a2 - λ5a4 - λ5a5 = 0) ^ (λ2a6 - λ3 + λ4(-a2 - a3 - 1) + λ5(-a5 - a6 - 1) = −λ))
```

### Statement 3

Statement 3 is simpler than Statement 2 and has a lot of repeated calculation, but I don't have a paper or book to guide me.

``I ^ x >= 0 => y > 0`` becomes ``(a1x + a2y + a3 >= 0 ∨ a4x + a5y + a6 >= 0) ^ (x >= 0) => y > 0`` by substitution.

More substituion to begin preparing for Farkas' lemma:
```
e1 = a1x + a2y + a3
e2 = a4x + a5y + a6
e3 = x
e4 = y - 1

(e1 >= 0 V e2 >= 0) ^ (e3 >= 0) => e4 >= 0

changing implies into a not and an or:
!((e1 >= 0 V e2 >= 0) ^ (e3 >= 0)) V e4 >= 0
```

De'morgan's law twice:
```
!((e1 >= 0 V e2 >= 0) ^ (e3 >= 0)) V e4 >= 0

becomes:
!(e1 >= 0 V e2 >= 0) V !(e3 >= 0) V e4 >= 0

which becomes:
(!(e1 >= 0) ^ !(e2 >= 0)) V !(e3 >= 0) V e4 >= 0
```

Distributing the and in order to get to CNF:
```
(!(e1 >= 0) V !(e3 >= 0) V e4 >= 0) ^ (!(e2 >= 0) V !(e3 >= 0) V e4 >= 0)
```

Double negation in order to do De'Morgan's again to be in form required by Farkas' lemma:
```
!!(!(e1 >= 0) V !(e3 >= 0) V e4 >= 0) ^ !!(!(e2 >= 0) V !(e3 >= 0) V e4 >= 0)

De'Morgan's:
!(e1 >= 0 ^ e3 >= 0 ^ !(e4 >= 0)) ^ !(e2 >= 0 ^ e3 >= 0 ^ !(e4 >= 0))
```

Doing the same trick as before in order to make each piece into non-negated expression appropriate for Farkas' lemma:
```
e4 >= 0 becomes !(-e4 - 1 >= 0)
etc...

resulting in:
!(e1 >= 0 ^ e3 >= 0 ^ (-e4 - 1 >= 0)) ^ (e2 >= 0 ^ e3 >= 0 ^ (-e4 - 1 >= 0))
```

Applying Farkas' lemma to each part. The (previously implied, now shown) universal quantifier can be pushed down into the and statement, allowing this.
```
∀x,y !(e1 >= 0 ^ e3 >= 0 ^ (-e4 - 1 >= 0)) ^ (e2 >= 0 ^ e3 >= 0 ^ (-e4 - 1 >= 0))

pushing down the quantifier, since it's universal with an and this doesn't change the meaning:
(∀x,y !(e1 >= 0 ^ e3 >= 0 ^ (-e4 - 1 >= 0))) ^ (∀x,y (e2 >= 0 ^ e3 >= 0 ^ (-e4 - 1 >= 0)))

Farkas' lemma:
(∃λ > 0, λ1,λ3,λ4 >= 0(∀x,y λ1e1 + λ3e3 + λ4(-e4 - 1) = −λ)) ^ (∃λ > 0, λ2,λ3,λ4 >= 0(∀x,y λ2e2 + λ3e3 + λ4(-e4 - 1) = −λ))
```

Looking at the inner part of the first term:
```
λ1e1 + λ3e3 + λ4(-e4 - 1) = −λ

e1 = a1x + a2y + a3
e2 = a4x + a5y + a6
e3 = x
e4 = y - 1

putting the e's back in:
λ1(a1x + a2y + a3) + λ3x - λ4y = −λ
```

Same process as before:
```
∀x,y λ1(a1x + a2y + a3) + λ3x - λ4y = −λ

terms with x: λ1a1x + λ3x
resulting expression: λ1a1 + λ3 = 0

terms with y: λ1a2y - λ4y
resulting expression: λ1a2 - λ4 = 0

terms without x or y: λ1a3 = −λ

final expression (I think?):
∃λ > 0, λ1,λ3,λ4 >= 0 ((λ1a1 + λ3 = 0) ^ (λ1a2 - λ4 = 0) ^ (λ1a3 = −λ))
```

Looking at the inner part of the second term:
```
λ2e2 + λ3e3 + λ4(-e4 - 1) = −λ

e1 = a1x + a2y + a3
e2 = a4x + a5y + a6
e3 = x
e4 = y - 1

putting the e's back in:
λ2(a4x + a5y + a6) + λ3x - λ4y = −λ
```

Same process as before (again):
```
∀x,y λ2(a4x + a5y + a6) + λ3x - λ4y = −λ

terms with x: λ2a4x + λ3x
resulting expression: λ2a4 + λ3 = 0

terms with y: λ2a5y - λ4y
resulting expression: λ2a5 - λ4 = 0

terms without x or y: λ2a6 = −λ

final expression (I think?):
∃λ > 0, λ2,λ3,λ4 >= 0 ((λ2a4 + λ3 = 0) ^ (λ2a5 - λ4 = 0) ^ (λ2a6 = −λ))
```

Once again, the final outcome is the and of two statements:
```
∃λ > 0, λ1,λ3,λ4 >= 0 ((λ1a1 + λ3 = 0) ^ (λ1a2 - λ4 = 0) ^ (λ1a3 = −λ))
and
∃λ > 0, λ2,λ3,λ4 >= 0 ((λ2a4 + λ3 = 0) ^ (λ2a5 - λ4 = 0) ^ (λ2a6 = −λ))
```

### Putting it all together

The results of the previous statements were:
```
Statement 1:
∃λ > 0, λ1,λ2 >= 0 ((-a2λ1 - a5λ2 = 0) ^ (50a1λ1 - a3λ1 − λ1 + 50a4λ2 - a6λ2 − λ2 = −λ))

Statement 2:
∃λ > 0, λ1,λ3,λ4,λ5 >= 0 ((λ1a1 - λ3 - λ4a1 - λ5a4 = 0) ^ (λ1a2 - λ4a1 - λ4a2 - λ5a4 - λ5a5 = 0) ^ (λ1a3 - λ3 + λ4(-a2 - a3 - 1) + λ5(-a5 - a6 - 1) = −λ))
and
∃λ > 0, λ2,λ3,λ4,λ5 >= 0 ((λ2a4 - λ3 - λ4a1 - λ5a4 = 0) ^ (λ2a5 - λ4a1 - λ4a2 - λ5a4 - λ5a5 = 0) ^ (λ2a6 - λ3 + λ4(-a2 - a3 - 1) + λ5(-a5 - a6 - 1) = −λ))

Statement 3:
∃λ > 0, λ1,λ3,λ4 >= 0 ((λ1a1 + λ3 = 0) ^ (λ1a2 - λ4 = 0) ^ (λ1a3 = −λ))
and
∃λ > 0, λ2,λ3,λ4 >= 0 ((λ2a4 + λ3 = 0) ^ (λ2a5 - λ4 = 0) ^ (λ2a6 = −λ))
```

The code I used to run this through z3 is in this github (it's messy, but I think it's correct).

## Results

As I have it defined, the problem seems under-constrained. When 
