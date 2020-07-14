---
src       : "src/plfa/part1/Induction.lagda.md"
title     : "Induction: Proof by Induction"
layout    : page
prev      : /Naturals/
permalink : /Induction/
next      : /Relations/
---

{% raw %}<pre class="Agda"><a id="146" class="Keyword">module</a> <a id="153" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html" class="Module">plfa.part1.Induction</a> <a id="174" class="Keyword">where</a>
</pre>{% endraw %}
> Induction makes you feel guilty for getting something out of nothing
> ... but it is one of the greatest ideas of civilization.
> -- Herbert Wilf

Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of _inductive datatypes_ are proved by
_induction_.


## Imports

We require equality as in the previous chapter, plus the naturals
and some operations upon them.  We also import a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below:
{% raw %}<pre class="Agda"><a id="769" class="Keyword">import</a> <a id="776" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="814" class="Symbol">as</a> <a id="817" class="Module">Eq</a>
<a id="820" class="Keyword">open</a> <a id="825" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="828" class="Keyword">using</a> <a id="834" class="Symbol">(</a><a id="835" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="838" class="Symbol">;</a> <a id="840" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="844" class="Symbol">;</a> <a id="846" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="850" class="Symbol">;</a> <a id="852" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="855" class="Symbol">)</a>
<a id="857" class="Keyword">open</a> <a id="862" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="877" class="Keyword">using</a> <a id="883" class="Symbol">(</a><a id="884" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="890" class="Symbol">;</a> <a id="892" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="897" class="Symbol">;</a> <a id="899" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="905" class="Symbol">;</a> <a id="907" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="909" class="Symbol">)</a>
<a id="911" class="Keyword">open</a> <a id="916" class="Keyword">import</a> <a id="923" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="932" class="Keyword">using</a> <a id="938" class="Symbol">(</a><a id="939" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="940" class="Symbol">;</a> <a id="942" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="946" class="Symbol">;</a> <a id="948" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="951" class="Symbol">;</a> <a id="953" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="956" class="Symbol">;</a> <a id="958" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="961" class="Symbol">;</a> <a id="963" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="966" class="Symbol">)</a>
</pre>{% endraw %}

## Properties of operators

Operators pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Identity_.   Operator `+` has left identity `0` if `0 + n ≡ n`, and
  right identity `0` if `n + 0 ≡ n`, for all `n`. A value that is both
  a left and right identity is just called an identity. Identity is also
  sometimes called _unit_.

* _Associativity_.   Operator `+` is associative if the location
  of parentheses does not matter: `(m + n) + p ≡ m + (n + p)`,
  for all `m`, `n`, and `p`.

* _Commutativity_.   Operator `+` is commutative if order of
  arguments does not matter: `m + n ≡ n + m`, for all `m` and `n`.

* _Distributivity_.   Operator `*` distributes over operator `+` from the
  left if `(m + n) * p ≡ (m * p) + (n * p)`, for all `m`, `n`, and `p`,
  and from the right if `m * (p + q) ≡ (m * p) + (m * q)`, for all `m`,
  `p`, and `q`.

Addition has identity `0` and multiplication has identity `1`;
addition and multiplication are both associative and commutative;
and multiplication distributes over addition.

If you ever bump into an operator at a party, you now know how
to make small talk, by asking whether it has a unit and is
associative or commutative.  If you bump into two operators, you
might ask them if one distributes over the other.

Less frivolously, if you ever bump into an operator while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it has an identity, is associative or commutative, or
distributes over another operator.  A careful author will often call
out these properties---or their lack---for instance by pointing out
that a newly introduced operator is associative but not commutative.

#### Exercise `operators` (practice) {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

Give an example of an operator that has an identity and is
associative but is not commutative.

{% raw %}<pre class="Agda"><a id="2992" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Associativity

One property of addition is that it is _associative_, that is, that the
location of the parentheses does not matter:

    (m + n) + p ≡ m + (n + p)

Here `m`, `n`, and `p` are variables that range over all natural numbers.

We can test the proposition by choosing specific numbers for the three
variables:
{% raw %}<pre class="Agda"><a id="3349" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#3349" class="Function">_</a> <a id="3351" class="Symbol">:</a> <a id="3353" class="Symbol">(</a><a id="3354" class="Number">3</a> <a id="3356" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3358" class="Number">4</a><a id="3359" class="Symbol">)</a> <a id="3361" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3363" class="Number">5</a> <a id="3365" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="3367" class="Number">3</a> <a id="3369" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3371" class="Symbol">(</a><a id="3372" class="Number">4</a> <a id="3374" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3376" class="Number">5</a><a id="3377" class="Symbol">)</a>
<a id="3379" class="Symbol">_</a> <a id="3381" class="Symbol">=</a>
  <a id="3385" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="3395" class="Symbol">(</a><a id="3396" class="Number">3</a> <a id="3398" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3400" class="Number">4</a><a id="3401" class="Symbol">)</a> <a id="3403" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3405" class="Number">5</a>
  <a id="3409" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3417" class="Number">7</a> <a id="3419" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3421" class="Number">5</a>
  <a id="3425" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3433" class="Number">12</a>
  <a id="3438" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3446" class="Number">3</a> <a id="3448" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3450" class="Number">9</a>
  <a id="3454" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="3462" class="Number">3</a> <a id="3464" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3466" class="Symbol">(</a><a id="3467" class="Number">4</a> <a id="3469" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="3471" class="Number">5</a><a id="3472" class="Symbol">)</a>
  <a id="3476" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}Here we have displayed the computation as a chain of equations,
one term to a line.  It is often easiest to read such chains from the top down
until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.

The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But---since there are an infinite number of
naturals---testing can never be complete.  Is there any way we can be
sure that associativity holds for _all_ the natural numbers?

The answer is yes! We can prove a property holds for all naturals using
_proof by induction_.


## Proof by induction

Recall the definition of natural numbers consists of a _base case_
which tells us that `zero` is a natural, and an _inductive case_
which tells us that if `m` is a natural then `suc m` is also a natural.

Proof by induction follows the structure of this definition.  To prove
a property of natural numbers by induction, we need to prove two cases.
First is the _base case_, where we show the property holds for `zero`.
Second is the _inductive case_, where we assume the property holds for
an arbitrary natural `m` (we call this the _inductive hypothesis_), and
then show that the property must also hold for `suc m`.

If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:

    ------
    P zero

    P m
    ---------
    P (suc m)

Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis---namely that `P` holds for `m`---then it follows that
`P` also holds for `suc m`.

Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties:

    -- In the beginning, no properties are known.

Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply:

    -- On the first day, one property is known.
    P zero

Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today:

    -- On the second day, two properties are known.
    P zero
    P (suc zero)

And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new:

    -- On the third day, three properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))

You've got the hang of it by now:

    -- On the fourth day, four properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

The process continues.  On the _n_'th day there will be _n_ distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day _n+1_.


## Our first proof: associativity

To prove associativity, we take `P m` to be the property:

    (m + n) + p ≡ m + (n + p)

Here `n` and `p` are arbitrary natural numbers, so if we can show the
equation holds for all `m` it will also hold for all `n` and `p`.
The appropriate instances of the inference rules are:

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ suc m + (n + p)

If we can demonstrate both of these, then associativity of addition
follows by induction.

Here is the proposition's statement and proof:
{% raw %}<pre class="Agda"><a id="+-assoc"></a><a id="7704" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7704" class="Function">+-assoc</a> <a id="7712" class="Symbol">:</a> <a id="7714" class="Symbol">∀</a> <a id="7716" class="Symbol">(</a><a id="7717" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7717" class="Bound">m</a> <a id="7719" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7719" class="Bound">n</a> <a id="7721" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7721" class="Bound">p</a> <a id="7723" class="Symbol">:</a> <a id="7725" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="7726" class="Symbol">)</a> <a id="7728" class="Symbol">→</a> <a id="7730" class="Symbol">(</a><a id="7731" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7717" class="Bound">m</a> <a id="7733" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7735" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7719" class="Bound">n</a><a id="7736" class="Symbol">)</a> <a id="7738" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7740" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7721" class="Bound">p</a> <a id="7742" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="7744" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7717" class="Bound">m</a> <a id="7746" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7748" class="Symbol">(</a><a id="7749" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7719" class="Bound">n</a> <a id="7751" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7753" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7721" class="Bound">p</a><a id="7754" class="Symbol">)</a>
<a id="7756" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7704" class="Function">+-assoc</a> <a id="7764" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="7769" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7769" class="Bound">n</a> <a id="7771" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7771" class="Bound">p</a> <a id="7773" class="Symbol">=</a>
  <a id="7777" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="7787" class="Symbol">(</a><a id="7788" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="7793" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7795" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7769" class="Bound">n</a><a id="7796" class="Symbol">)</a> <a id="7798" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7800" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7771" class="Bound">p</a>
  <a id="7804" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="7812" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7769" class="Bound">n</a> <a id="7814" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7816" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7771" class="Bound">p</a>
  <a id="7820" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="7828" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="7833" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7835" class="Symbol">(</a><a id="7836" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7769" class="Bound">n</a> <a id="7838" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7840" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7771" class="Bound">p</a><a id="7841" class="Symbol">)</a>
  <a id="7845" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="7847" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7704" class="Function">+-assoc</a> <a id="7855" class="Symbol">(</a><a id="7856" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7860" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7860" class="Bound">m</a><a id="7861" class="Symbol">)</a> <a id="7863" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7863" class="Bound">n</a> <a id="7865" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7865" class="Bound">p</a> <a id="7867" class="Symbol">=</a>
  <a id="7871" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="7881" class="Symbol">(</a><a id="7882" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7886" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7860" class="Bound">m</a> <a id="7888" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7890" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7863" class="Bound">n</a><a id="7891" class="Symbol">)</a> <a id="7893" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7895" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7865" class="Bound">p</a>
  <a id="7899" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="7907" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7911" class="Symbol">(</a><a id="7912" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7860" class="Bound">m</a> <a id="7914" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7916" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7863" class="Bound">n</a><a id="7917" class="Symbol">)</a> <a id="7919" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7921" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7865" class="Bound">p</a>
  <a id="7925" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="7933" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7937" class="Symbol">((</a><a id="7939" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7860" class="Bound">m</a> <a id="7941" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7943" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7863" class="Bound">n</a><a id="7944" class="Symbol">)</a> <a id="7946" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7948" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7865" class="Bound">p</a><a id="7949" class="Symbol">)</a>
  <a id="7953" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="7956" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="7961" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7965" class="Symbol">(</a><a id="7966" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7704" class="Function">+-assoc</a> <a id="7974" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7860" class="Bound">m</a> <a id="7976" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7863" class="Bound">n</a> <a id="7978" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7865" class="Bound">p</a><a id="7979" class="Symbol">)</a> <a id="7981" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="7987" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7991" class="Symbol">(</a><a id="7992" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7860" class="Bound">m</a> <a id="7994" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="7996" class="Symbol">(</a><a id="7997" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7863" class="Bound">n</a> <a id="7999" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="8001" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7865" class="Bound">p</a><a id="8002" class="Symbol">))</a>
  <a id="8007" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="8015" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="8019" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7860" class="Bound">m</a> <a id="8021" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="8023" class="Symbol">(</a><a id="8024" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7863" class="Bound">n</a> <a id="8026" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="8028" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7865" class="Bound">p</a><a id="8029" class="Symbol">)</a>
  <a id="8033" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}We have named the proof `+-assoc`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.

Let's unpack this code.  The signature states that we are
defining the identifier `+-assoc` which provides evidence for the
proposition:

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p`
the equation `(m + n) + p ≡ m + (n + p)` holds.  Evidence for the proposition
is a function that accepts three natural numbers, binds them to `m`, `n`, and `p`,
and returns evidence for the corresponding instance of the equation.

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially.  Reading the chain of equations in the base case of the proof,
the top and bottom of the chain match the two sides of the equation to
be shown, and reading down from the top and up from the bottom takes us to
`n + p` in the middle.  No justification other than simplification is required.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    (m + n) + p ≡ m + (n + p)

Reading the chain of equations in the inductive case of the proof, the
top and bottom of the chain match the two sides of the equation to be
shown, and reading down from the top and up from the bottom takes us
to the simplified equation above. The remaining equation, does not follow
from simplification alone, so we use an additional operator for chain
reasoning, `_≡⟨_⟩_`, where a justification for the equation appears
within angle brackets.  The justification given is:

    ⟨ cong suc (+-assoc m n p) ⟩

Here, the recursive invocation `+-assoc m n p` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.

A relation is said to be a _congruence_ for a given function if it is
preserved by applying that function.  If `e` is evidence that `x ≡ y`,
then `cong f e` is evidence that `f x ≡ f y`, for any function `f`.

Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are defining, `+-assoc m n p`.
As with addition, this is well founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `assoc (suc m) n p` is proved using `assoc m n p`.
The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.

## Induction as recursion

As a concrete example of how induction corresponds to recursion, here
is the computation that occurs when instantiating `m` to `2` in the
proof of associativity.

{% raw %}<pre class="Agda"><a id="+-assoc-2"></a><a id="11057" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11057" class="Function">+-assoc-2</a> <a id="11067" class="Symbol">:</a> <a id="11069" class="Symbol">∀</a> <a id="11071" class="Symbol">(</a><a id="11072" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11072" class="Bound">n</a> <a id="11074" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11074" class="Bound">p</a> <a id="11076" class="Symbol">:</a> <a id="11078" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11079" class="Symbol">)</a> <a id="11081" class="Symbol">→</a> <a id="11083" class="Symbol">(</a><a id="11084" class="Number">2</a> <a id="11086" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11088" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11072" class="Bound">n</a><a id="11089" class="Symbol">)</a> <a id="11091" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11093" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11074" class="Bound">p</a> <a id="11095" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11097" class="Number">2</a> <a id="11099" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11101" class="Symbol">(</a><a id="11102" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11072" class="Bound">n</a> <a id="11104" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11106" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11074" class="Bound">p</a><a id="11107" class="Symbol">)</a>
<a id="11109" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11057" class="Function">+-assoc-2</a> <a id="11119" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11119" class="Bound">n</a> <a id="11121" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11121" class="Bound">p</a> <a id="11123" class="Symbol">=</a>
  <a id="11127" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="11137" class="Symbol">(</a><a id="11138" class="Number">2</a> <a id="11140" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11142" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11119" class="Bound">n</a><a id="11143" class="Symbol">)</a> <a id="11145" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11147" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11121" class="Bound">p</a>
  <a id="11151" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11159" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11163" class="Symbol">(</a><a id="11164" class="Number">1</a> <a id="11166" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11168" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11119" class="Bound">n</a><a id="11169" class="Symbol">)</a> <a id="11171" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11173" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11121" class="Bound">p</a>
  <a id="11177" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11185" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11189" class="Symbol">((</a><a id="11191" class="Number">1</a> <a id="11193" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11195" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11119" class="Bound">n</a><a id="11196" class="Symbol">)</a> <a id="11198" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11200" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11121" class="Bound">p</a><a id="11201" class="Symbol">)</a>
  <a id="11205" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="11208" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="11213" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11217" class="Symbol">(</a><a id="11218" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11293" class="Function">+-assoc-1</a> <a id="11228" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11119" class="Bound">n</a> <a id="11230" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11121" class="Bound">p</a><a id="11231" class="Symbol">)</a> <a id="11233" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="11239" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11243" class="Symbol">(</a><a id="11244" class="Number">1</a> <a id="11246" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11248" class="Symbol">(</a><a id="11249" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11119" class="Bound">n</a> <a id="11251" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11253" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11121" class="Bound">p</a><a id="11254" class="Symbol">))</a>
  <a id="11259" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="11267" class="Number">2</a> <a id="11269" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11271" class="Symbol">(</a><a id="11272" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11119" class="Bound">n</a> <a id="11274" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11276" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11121" class="Bound">p</a><a id="11277" class="Symbol">)</a>
  <a id="11281" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
  <a id="11285" class="Keyword">where</a>
  <a id="11293" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11293" class="Function">+-assoc-1</a> <a id="11303" class="Symbol">:</a> <a id="11305" class="Symbol">∀</a> <a id="11307" class="Symbol">(</a><a id="11308" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11308" class="Bound">n</a> <a id="11310" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11310" class="Bound">p</a> <a id="11312" class="Symbol">:</a> <a id="11314" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11315" class="Symbol">)</a> <a id="11317" class="Symbol">→</a> <a id="11319" class="Symbol">(</a><a id="11320" class="Number">1</a> <a id="11322" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11324" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11308" class="Bound">n</a><a id="11325" class="Symbol">)</a> <a id="11327" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11329" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11310" class="Bound">p</a> <a id="11331" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11333" class="Number">1</a> <a id="11335" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11337" class="Symbol">(</a><a id="11338" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11308" class="Bound">n</a> <a id="11340" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11342" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11310" class="Bound">p</a><a id="11343" class="Symbol">)</a>
  <a id="11347" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11293" class="Function">+-assoc-1</a> <a id="11357" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11357" class="Bound">n</a> <a id="11359" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11359" class="Bound">p</a> <a id="11361" class="Symbol">=</a>
    <a id="11367" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
      <a id="11379" class="Symbol">(</a><a id="11380" class="Number">1</a> <a id="11382" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11384" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11357" class="Bound">n</a><a id="11385" class="Symbol">)</a> <a id="11387" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11389" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11359" class="Bound">p</a>
    <a id="11395" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="11405" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11409" class="Symbol">(</a><a id="11410" class="Number">0</a> <a id="11412" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11414" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11357" class="Bound">n</a><a id="11415" class="Symbol">)</a> <a id="11417" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11419" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11359" class="Bound">p</a>
    <a id="11425" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="11435" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11439" class="Symbol">((</a><a id="11441" class="Number">0</a> <a id="11443" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11445" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11357" class="Bound">n</a><a id="11446" class="Symbol">)</a> <a id="11448" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11450" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11359" class="Bound">p</a><a id="11451" class="Symbol">)</a>
    <a id="11457" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="11460" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="11465" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11469" class="Symbol">(</a><a id="11470" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11557" class="Function">+-assoc-0</a> <a id="11480" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11357" class="Bound">n</a> <a id="11482" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11359" class="Bound">p</a><a id="11483" class="Symbol">)</a> <a id="11485" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
      <a id="11493" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11497" class="Symbol">(</a><a id="11498" class="Number">0</a> <a id="11500" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11502" class="Symbol">(</a><a id="11503" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11357" class="Bound">n</a> <a id="11505" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11507" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11359" class="Bound">p</a><a id="11508" class="Symbol">))</a>
    <a id="11515" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
      <a id="11525" class="Number">1</a> <a id="11527" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11529" class="Symbol">(</a><a id="11530" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11357" class="Bound">n</a> <a id="11532" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11534" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11359" class="Bound">p</a><a id="11535" class="Symbol">)</a>
    <a id="11541" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
    <a id="11547" class="Keyword">where</a>
    <a id="11557" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11557" class="Function">+-assoc-0</a> <a id="11567" class="Symbol">:</a> <a id="11569" class="Symbol">∀</a> <a id="11571" class="Symbol">(</a><a id="11572" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11572" class="Bound">n</a> <a id="11574" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11574" class="Bound">p</a> <a id="11576" class="Symbol">:</a> <a id="11578" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11579" class="Symbol">)</a> <a id="11581" class="Symbol">→</a> <a id="11583" class="Symbol">(</a><a id="11584" class="Number">0</a> <a id="11586" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11588" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11572" class="Bound">n</a><a id="11589" class="Symbol">)</a> <a id="11591" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11593" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11574" class="Bound">p</a> <a id="11595" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11597" class="Number">0</a> <a id="11599" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11601" class="Symbol">(</a><a id="11602" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11572" class="Bound">n</a> <a id="11604" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11606" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11574" class="Bound">p</a><a id="11607" class="Symbol">)</a>
    <a id="11613" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11557" class="Function">+-assoc-0</a> <a id="11623" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11623" class="Bound">n</a> <a id="11625" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11625" class="Bound">p</a> <a id="11627" class="Symbol">=</a>
      <a id="11635" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
        <a id="11649" class="Symbol">(</a><a id="11650" class="Number">0</a> <a id="11652" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11654" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11623" class="Bound">n</a><a id="11655" class="Symbol">)</a> <a id="11657" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11659" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11625" class="Bound">p</a>
      <a id="11667" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
        <a id="11679" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11623" class="Bound">n</a> <a id="11681" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11683" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11625" class="Bound">p</a>
      <a id="11691" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
        <a id="11703" class="Number">0</a> <a id="11705" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11707" class="Symbol">(</a><a id="11708" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11623" class="Bound">n</a> <a id="11710" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="11712" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#11625" class="Bound">p</a><a id="11713" class="Symbol">)</a>
      <a id="11721" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}

## Terminology and notation

The symbol `∀` appears in the statement of associativity to indicate that
it holds for all numbers `m`, `n`, and `p`.  We refer to `∀` as the _universal
quantifier_, and it is discussed further in Chapter [Quantifiers]({{ site.baseurl }}/Quantifiers/).

Evidence for a universal quantifier is a function.  The notations

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

and

    +-assoc : ∀ (m : ℕ) → ∀ (n : ℕ) → ∀ (p : ℕ) → (m + n) + p ≡ m + (n + p)

are equivalent. They differ from a function type such as `ℕ → ℕ → ℕ`
in that variables are associated with the each argument type, and the
result type may mention (or depend upon) these variables; hence they
are called _dependent functions_.


## Our second proof: commutativity

Another important property of addition is that it is _commutative_, that is,
that the order of the operands does not matter:

    m + n ≡ n + m

The proof requires that we first demonstrate two lemmas.

### The first lemma

The base case of the definition of addition states that zero
is a left-identity:

    zero + n ≡ n

Our first lemma states that zero is also a right-identity:

    m + zero ≡ m

Here is the lemma's statement and proof:
{% raw %}<pre class="Agda"><a id="+-identityʳ"></a><a id="12945" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12945" class="Function">+-identityʳ</a> <a id="12957" class="Symbol">:</a> <a id="12959" class="Symbol">∀</a> <a id="12961" class="Symbol">(</a><a id="12962" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12962" class="Bound">m</a> <a id="12964" class="Symbol">:</a> <a id="12966" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12967" class="Symbol">)</a> <a id="12969" class="Symbol">→</a> <a id="12971" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12962" class="Bound">m</a> <a id="12973" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="12975" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="12980" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="12982" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12962" class="Bound">m</a>
<a id="12984" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12945" class="Function">+-identityʳ</a> <a id="12996" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="13001" class="Symbol">=</a>
  <a id="13005" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="13015" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="13020" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="13022" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="13029" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="13037" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="13044" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="13046" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12945" class="Function">+-identityʳ</a> <a id="13058" class="Symbol">(</a><a id="13059" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13063" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13063" class="Bound">m</a><a id="13064" class="Symbol">)</a> <a id="13066" class="Symbol">=</a>
  <a id="13070" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="13080" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13084" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13063" class="Bound">m</a> <a id="13086" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="13088" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="13095" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="13103" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13107" class="Symbol">(</a><a id="13108" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13063" class="Bound">m</a> <a id="13110" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="13112" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="13116" class="Symbol">)</a>
  <a id="13120" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="13123" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="13128" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13132" class="Symbol">(</a><a id="13133" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12945" class="Function">+-identityʳ</a> <a id="13145" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13063" class="Bound">m</a><a id="13146" class="Symbol">)</a> <a id="13148" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="13154" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13158" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#13063" class="Bound">m</a>
  <a id="13162" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}The signature states that we are defining the identifier `+-identityʳ` which
provides evidence for the proposition:

    ∀ (m : ℕ) → m + zero ≡ m

Evidence for the proposition is a function that accepts a natural
number, binds it to `m`, and returns evidence for the corresponding
instance of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + zero ≡ zero

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    (suc m) + zero = suc m

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + zero) = suc m

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + zero ≡ m

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation above.  The remaining
equation has the justification:

    ⟨ cong suc (+-identityʳ m) ⟩

Here, the recursive invocation `+-identityʳ m` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the first lemma.

### The second lemma

The inductive case of the definition of addition pushes `suc` on the
first argument to the outside:

    suc m + n ≡ suc (m + n)

Our second lemma does the same for `suc` on the second argument:

    m + suc n ≡ suc (m + n)

Here is the lemma's statement and proof:
{% raw %}<pre class="Agda"><a id="+-suc"></a><a id="14602" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14602" class="Function">+-suc</a> <a id="14608" class="Symbol">:</a> <a id="14610" class="Symbol">∀</a> <a id="14612" class="Symbol">(</a><a id="14613" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14613" class="Bound">m</a> <a id="14615" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14615" class="Bound">n</a> <a id="14617" class="Symbol">:</a> <a id="14619" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="14620" class="Symbol">)</a> <a id="14622" class="Symbol">→</a> <a id="14624" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14613" class="Bound">m</a> <a id="14626" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14628" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14632" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14615" class="Bound">n</a> <a id="14634" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="14636" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14640" class="Symbol">(</a><a id="14641" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14613" class="Bound">m</a> <a id="14643" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14645" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14615" class="Bound">n</a><a id="14646" class="Symbol">)</a>
<a id="14648" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14602" class="Function">+-suc</a> <a id="14654" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="14659" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14659" class="Bound">n</a> <a id="14661" class="Symbol">=</a>
  <a id="14665" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="14675" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="14680" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14682" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14686" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14659" class="Bound">n</a>
  <a id="14690" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="14698" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14702" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14659" class="Bound">n</a>
  <a id="14706" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="14714" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14718" class="Symbol">(</a><a id="14719" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="14724" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14726" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14659" class="Bound">n</a><a id="14727" class="Symbol">)</a>
  <a id="14731" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="14733" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14602" class="Function">+-suc</a> <a id="14739" class="Symbol">(</a><a id="14740" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14744" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14744" class="Bound">m</a><a id="14745" class="Symbol">)</a> <a id="14747" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14747" class="Bound">n</a> <a id="14749" class="Symbol">=</a>
  <a id="14753" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="14763" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14767" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14744" class="Bound">m</a> <a id="14769" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14771" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14775" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14747" class="Bound">n</a>
  <a id="14779" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="14787" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14791" class="Symbol">(</a><a id="14792" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14744" class="Bound">m</a> <a id="14794" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14796" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14800" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14747" class="Bound">n</a><a id="14801" class="Symbol">)</a>
  <a id="14805" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="14808" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="14813" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14817" class="Symbol">(</a><a id="14818" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14602" class="Function">+-suc</a> <a id="14824" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14744" class="Bound">m</a> <a id="14826" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14747" class="Bound">n</a><a id="14827" class="Symbol">)</a> <a id="14829" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="14835" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14839" class="Symbol">(</a><a id="14840" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14844" class="Symbol">(</a><a id="14845" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14744" class="Bound">m</a> <a id="14847" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14849" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14747" class="Bound">n</a><a id="14850" class="Symbol">))</a>
  <a id="14855" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="14863" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14867" class="Symbol">(</a><a id="14868" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14872" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14744" class="Bound">m</a> <a id="14874" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="14876" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14747" class="Bound">n</a><a id="14877" class="Symbol">)</a>
  <a id="14881" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}The signature states that we are defining the identifier `+-suc` which provides
evidence for the proposition:

    ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

Evidence for the proposition is a function that accepts two natural numbers,
binds them to `m` and `n`, and returns evidence for the corresponding instance
of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + suc n ≡ suc (zero + n)

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    suc m + suc n ≡ suc (suc m + n)

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + suc n) ≡ suc (suc (m + n))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + suc n ≡ suc (m + n)

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation in the middle.  The remaining
equation has the justification:

    ⟨ cong suc (+-suc m n) ⟩

Here, the recursive invocation `+-suc m n` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the second lemma.

### The proposition

Finally, here is our proposition's statement and proof:
{% raw %}<pre class="Agda"><a id="+-comm"></a><a id="16175" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16175" class="Function">+-comm</a> <a id="16182" class="Symbol">:</a> <a id="16184" class="Symbol">∀</a> <a id="16186" class="Symbol">(</a><a id="16187" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16187" class="Bound">m</a> <a id="16189" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16189" class="Bound">n</a> <a id="16191" class="Symbol">:</a> <a id="16193" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16194" class="Symbol">)</a> <a id="16196" class="Symbol">→</a> <a id="16198" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16187" class="Bound">m</a> <a id="16200" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16202" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16189" class="Bound">n</a> <a id="16204" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16206" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16189" class="Bound">n</a> <a id="16208" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16210" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16187" class="Bound">m</a>
<a id="16212" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16175" class="Function">+-comm</a> <a id="16219" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16219" class="Bound">m</a> <a id="16221" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="16226" class="Symbol">=</a>
  <a id="16230" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="16240" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16219" class="Bound">m</a> <a id="16242" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16244" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
  <a id="16251" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16254" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#12945" class="Function">+-identityʳ</a> <a id="16266" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16219" class="Bound">m</a> <a id="16268" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="16274" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16219" class="Bound">m</a>
  <a id="16278" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16286" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="16291" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16293" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16219" class="Bound">m</a>
  <a id="16297" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
<a id="16299" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16175" class="Function">+-comm</a> <a id="16306" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16306" class="Bound">m</a> <a id="16308" class="Symbol">(</a><a id="16309" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16313" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16313" class="Bound">n</a><a id="16314" class="Symbol">)</a> <a id="16316" class="Symbol">=</a>
  <a id="16320" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="16330" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16306" class="Bound">m</a> <a id="16332" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16334" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16338" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16313" class="Bound">n</a>
  <a id="16342" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16345" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#14602" class="Function">+-suc</a> <a id="16351" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16306" class="Bound">m</a> <a id="16353" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16313" class="Bound">n</a> <a id="16355" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="16361" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16365" class="Symbol">(</a><a id="16366" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16306" class="Bound">m</a> <a id="16368" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16370" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16313" class="Bound">n</a><a id="16371" class="Symbol">)</a>
  <a id="16375" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="16378" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="16383" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16387" class="Symbol">(</a><a id="16388" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16175" class="Function">+-comm</a> <a id="16395" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16306" class="Bound">m</a> <a id="16397" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16313" class="Bound">n</a><a id="16398" class="Symbol">)</a> <a id="16400" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="16406" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16410" class="Symbol">(</a><a id="16411" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16313" class="Bound">n</a> <a id="16413" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16415" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16306" class="Bound">m</a><a id="16416" class="Symbol">)</a>
  <a id="16420" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">≡⟨⟩</a>
    <a id="16428" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16432" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16313" class="Bound">n</a> <a id="16434" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="16436" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#16306" class="Bound">m</a>
  <a id="16440" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}The first line states that we are defining the identifier
`+-comm` which provides evidence for the proposition:

    ∀ (m n : ℕ) → m + n ≡ n + m

Evidence for the proposition is a function that accepts two
natural numbers, binds them to `m` and `n`, and returns evidence for the
corresponding instance of the equation.  The proof is by
induction on `n`.  (Not on `m` this time!)

For the base case, we must show:

    m + zero ≡ zero + m

Simplifying both sides with the base case of addition yields the equation:

    m + zero ≡ m

The remaining equation has the justification `⟨ +-identityʳ m ⟩`,
which invokes the first lemma.

For the inductive case, we must show:

    m + suc n ≡ suc n + m

Simplifying both sides with the inductive case of addition yields the equation:

    m + suc n ≡ suc (n + m)

We show this in two steps.  First, we have:

    m + suc n ≡ suc (m + n)

which is justified by the second lemma, `⟨ +-suc m n ⟩`.  Then we
have

    suc (m + n) ≡ suc (n + m)

which is justified by congruence and the induction hypothesis,
`⟨ cong suc (+-comm m n) ⟩`.  This completes the proof.

Agda requires that identifiers are defined before they are used,
so we must present the lemmas before the main proposition, as we
have done above.  In practice, one will often attempt to prove
the main proposition first, and the equations required to do so
will suggest what lemmas to prove.


## Our first corollary: rearranging {#sections}

We can apply associativity to rearrange parentheses however we like.
Here is an example:
{% raw %}<pre class="Agda"><a id="+-rearrange"></a><a id="17986" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17986" class="Function">+-rearrange</a> <a id="17998" class="Symbol">:</a> <a id="18000" class="Symbol">∀</a> <a id="18002" class="Symbol">(</a><a id="18003" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18003" class="Bound">m</a> <a id="18005" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18005" class="Bound">n</a> <a id="18007" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18007" class="Bound">p</a> <a id="18009" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18009" class="Bound">q</a> <a id="18011" class="Symbol">:</a> <a id="18013" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18014" class="Symbol">)</a> <a id="18016" class="Symbol">→</a> <a id="18018" class="Symbol">(</a><a id="18019" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18003" class="Bound">m</a> <a id="18021" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18023" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18005" class="Bound">n</a><a id="18024" class="Symbol">)</a> <a id="18026" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18028" class="Symbol">(</a><a id="18029" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18007" class="Bound">p</a> <a id="18031" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18033" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18009" class="Bound">q</a><a id="18034" class="Symbol">)</a> <a id="18036" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="18038" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18003" class="Bound">m</a> <a id="18040" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18042" class="Symbol">(</a><a id="18043" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18005" class="Bound">n</a> <a id="18045" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18047" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18007" class="Bound">p</a><a id="18048" class="Symbol">)</a> <a id="18050" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18052" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18009" class="Bound">q</a>
<a id="18054" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#17986" class="Function">+-rearrange</a> <a id="18066" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18066" class="Bound">m</a> <a id="18068" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18068" class="Bound">n</a> <a id="18070" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18070" class="Bound">p</a> <a id="18072" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18072" class="Bound">q</a> <a id="18074" class="Symbol">=</a>
  <a id="18078" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin</a>
    <a id="18088" class="Symbol">(</a><a id="18089" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18066" class="Bound">m</a> <a id="18091" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18093" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18068" class="Bound">n</a><a id="18094" class="Symbol">)</a> <a id="18096" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18098" class="Symbol">(</a><a id="18099" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18070" class="Bound">p</a> <a id="18101" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18103" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18072" class="Bound">q</a><a id="18104" class="Symbol">)</a>
  <a id="18108" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="18111" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7704" class="Function">+-assoc</a> <a id="18119" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18066" class="Bound">m</a> <a id="18121" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18068" class="Bound">n</a> <a id="18123" class="Symbol">(</a><a id="18124" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18070" class="Bound">p</a> <a id="18126" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18128" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18072" class="Bound">q</a><a id="18129" class="Symbol">)</a> <a id="18131" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="18137" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18066" class="Bound">m</a> <a id="18139" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18141" class="Symbol">(</a><a id="18142" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18068" class="Bound">n</a> <a id="18144" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18146" class="Symbol">(</a><a id="18147" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18070" class="Bound">p</a> <a id="18149" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18151" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18072" class="Bound">q</a><a id="18152" class="Symbol">))</a>
  <a id="18157" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="18160" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="18165" class="Symbol">(</a><a id="18166" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18066" class="Bound">m</a> <a id="18168" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+_</a><a id="18170" class="Symbol">)</a> <a id="18172" class="Symbol">(</a><a id="18173" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a> <a id="18177" class="Symbol">(</a><a id="18178" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7704" class="Function">+-assoc</a> <a id="18186" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18068" class="Bound">n</a> <a id="18188" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18070" class="Bound">p</a> <a id="18190" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18072" class="Bound">q</a><a id="18191" class="Symbol">))</a> <a id="18194" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="18200" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18066" class="Bound">m</a> <a id="18202" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18204" class="Symbol">((</a><a id="18206" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18068" class="Bound">n</a> <a id="18208" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18210" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18070" class="Bound">p</a><a id="18211" class="Symbol">)</a> <a id="18213" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18215" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18072" class="Bound">q</a><a id="18216" class="Symbol">)</a>
  <a id="18220" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">≡⟨</a> <a id="18223" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a> <a id="18227" class="Symbol">(</a><a id="18228" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#7704" class="Function">+-assoc</a> <a id="18236" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18066" class="Bound">m</a> <a id="18238" class="Symbol">(</a><a id="18239" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18068" class="Bound">n</a> <a id="18241" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18243" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18070" class="Bound">p</a><a id="18244" class="Symbol">)</a> <a id="18246" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18072" class="Bound">q</a><a id="18247" class="Symbol">)</a> <a id="18249" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">⟩</a>
    <a id="18255" class="Symbol">(</a><a id="18256" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18066" class="Bound">m</a> <a id="18258" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18260" class="Symbol">(</a><a id="18261" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18068" class="Bound">n</a> <a id="18263" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18265" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18070" class="Bound">p</a><a id="18266" class="Symbol">))</a> <a id="18269" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18271" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#18072" class="Bound">q</a>
  <a id="18275" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">∎</a>
</pre>{% endraw %}No induction is required, we simply apply associativity twice.
A few points are worthy of note.

First, addition associates to the left, so `m + (n + p) + q`
stands for `(m + (n + p)) + q`.

Second, we use `sym` to interchange the sides of an equation.
Proposition `+-assoc n p q` shifts parentheses from right to left:

    (n + p) + q ≡ n + (p + q)

To shift them the other way, we use `sym (+-assoc n p q)`:

    n + (p + q) ≡ (n + p) + q

In general, if `e` provides evidence for `x ≡ y` then `sym e` provides
evidence for `y ≡ x`.

Third, Agda supports a variant of the _section_ notation introduced by
Richard Bird.  We write `(x +_)` for the function that applied to `y`
returns `x + y`.  Thus, applying the congruence `cong (m +_)` takes
the above equation into:

    m + (n + (p + q)) ≡ m + ((n + p) + q)

Similarly, we write `(_+ x)` for the function that applied to `y`
returns `y + x`; the same works for any infix operator.



## Creation, one last time

Returning to the proof of associativity, it may be helpful to view the inductive
proof (or, equivalently, the recursive definition) as a creation story.  This
time we are concerned with judgments asserting associativity:

     -- In the beginning, we know nothing about associativity.

Now, we apply the rules to all the judgments we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if `(m + n) + p ≡ m +
(n + p)` (on the day before today) then
`(suc m + n) + p ≡ suc m + (n + p)` (today).
We didn't know any judgments about associativity before today, so that
rule doesn't give us any new judgments:

    -- On the first day, we know about associativity of 0.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...

Then we repeat the process, so on the next day we know about all the
judgments from the day before, plus any judgments added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgments:

    -- On the second day, we know about associativity of 0 and 1.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

And we repeat the process again:

    -- On the third day, we know about associativity of 0, 1, and 2.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

You've got the hang of it by now:

    -- On the fourth day, we know about associativity of 0, 1, 2, and 3.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...

The process continues.  On the _m_'th day we will know all the
judgments where the first number is less than _m_.

There is also a completely finite approach to generating the same equations,
which is left as an exercise for the reader.

#### Exercise `finite-|-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the
first four days using a finite story of creation, as
[earlier]({{ site.baseurl }}/Naturals/#finite-creation).

{% raw %}<pre class="Agda"><a id="21693" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Associativity with rewrite

There is more than one way to skin a cat.  Here is a second proof of
associativity of addition in Agda, using `rewrite` rather than chains of
equations:
{% raw %}<pre class="Agda"><a id="+-assoc′"></a><a id="21909" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21909" class="Function">+-assoc′</a> <a id="21918" class="Symbol">:</a> <a id="21920" class="Symbol">∀</a> <a id="21922" class="Symbol">(</a><a id="21923" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21923" class="Bound">m</a> <a id="21925" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21925" class="Bound">n</a> <a id="21927" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21927" class="Bound">p</a> <a id="21929" class="Symbol">:</a> <a id="21931" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21932" class="Symbol">)</a> <a id="21934" class="Symbol">→</a> <a id="21936" class="Symbol">(</a><a id="21937" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21923" class="Bound">m</a> <a id="21939" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21941" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21925" class="Bound">n</a><a id="21942" class="Symbol">)</a> <a id="21944" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21946" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21927" class="Bound">p</a> <a id="21948" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="21950" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21923" class="Bound">m</a> <a id="21952" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21954" class="Symbol">(</a><a id="21955" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21925" class="Bound">n</a> <a id="21957" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="21959" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21927" class="Bound">p</a><a id="21960" class="Symbol">)</a>
<a id="21962" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21909" class="Function">+-assoc′</a> <a id="21971" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="21979" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21979" class="Bound">n</a> <a id="21981" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21981" class="Bound">p</a>                          <a id="22008" class="Symbol">=</a>  <a id="22011" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="22016" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21909" class="Function">+-assoc′</a> <a id="22025" class="Symbol">(</a><a id="22026" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="22030" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22030" class="Bound">m</a><a id="22031" class="Symbol">)</a> <a id="22033" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22033" class="Bound">n</a> <a id="22035" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22035" class="Bound">p</a>  <a id="22038" class="Keyword">rewrite</a> <a id="22046" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#21909" class="Function">+-assoc′</a> <a id="22055" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22030" class="Bound">m</a> <a id="22057" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22033" class="Bound">n</a> <a id="22059" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22035" class="Bound">p</a>  <a id="22062" class="Symbol">=</a>  <a id="22065" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially. The proof that a term is equal to itself is written `refl`.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

After rewriting with the inductive hypothesis these two terms are equal, and the
proof is again given by `refl`.  Rewriting by a given equation is indicated by
the keyword `rewrite` followed by a proof of that equation.  Rewriting avoids
not only chains of equations but also the need to invoke `cong`.


## Commutativity with rewrite

Here is a second proof of commutativity of addition, using `rewrite` rather than
chains of equations:
{% raw %}<pre class="Agda"><a id="+-identity′"></a><a id="22968" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22968" class="Function">+-identity′</a> <a id="22980" class="Symbol">:</a> <a id="22982" class="Symbol">∀</a> <a id="22984" class="Symbol">(</a><a id="22985" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22985" class="Bound">n</a> <a id="22987" class="Symbol">:</a> <a id="22989" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22990" class="Symbol">)</a> <a id="22992" class="Symbol">→</a> <a id="22994" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22985" class="Bound">n</a> <a id="22996" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="22998" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23003" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="23005" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22985" class="Bound">n</a>
<a id="23007" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22968" class="Function">+-identity′</a> <a id="23019" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23024" class="Symbol">=</a> <a id="23026" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="23031" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22968" class="Function">+-identity′</a> <a id="23043" class="Symbol">(</a><a id="23044" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23048" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23048" class="Bound">n</a><a id="23049" class="Symbol">)</a> <a id="23051" class="Keyword">rewrite</a> <a id="23059" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22968" class="Function">+-identity′</a> <a id="23071" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23048" class="Bound">n</a> <a id="23073" class="Symbol">=</a> <a id="23075" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="+-suc′"></a><a id="23081" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23081" class="Function">+-suc′</a> <a id="23088" class="Symbol">:</a> <a id="23090" class="Symbol">∀</a> <a id="23092" class="Symbol">(</a><a id="23093" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23093" class="Bound">m</a> <a id="23095" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23095" class="Bound">n</a> <a id="23097" class="Symbol">:</a> <a id="23099" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="23100" class="Symbol">)</a> <a id="23102" class="Symbol">→</a> <a id="23104" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23093" class="Bound">m</a> <a id="23106" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23108" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23112" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23095" class="Bound">n</a> <a id="23114" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="23116" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23120" class="Symbol">(</a><a id="23121" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23093" class="Bound">m</a> <a id="23123" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23125" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23095" class="Bound">n</a><a id="23126" class="Symbol">)</a>
<a id="23128" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23081" class="Function">+-suc′</a> <a id="23135" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23140" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23140" class="Bound">n</a> <a id="23142" class="Symbol">=</a> <a id="23144" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="23149" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23081" class="Function">+-suc′</a> <a id="23156" class="Symbol">(</a><a id="23157" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23161" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23161" class="Bound">m</a><a id="23162" class="Symbol">)</a> <a id="23164" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23164" class="Bound">n</a> <a id="23166" class="Keyword">rewrite</a> <a id="23174" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23081" class="Function">+-suc′</a> <a id="23181" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23161" class="Bound">m</a> <a id="23183" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23164" class="Bound">n</a> <a id="23185" class="Symbol">=</a> <a id="23187" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="+-comm′"></a><a id="23193" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23193" class="Function">+-comm′</a> <a id="23201" class="Symbol">:</a> <a id="23203" class="Symbol">∀</a> <a id="23205" class="Symbol">(</a><a id="23206" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23206" class="Bound">m</a> <a id="23208" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23208" class="Bound">n</a> <a id="23210" class="Symbol">:</a> <a id="23212" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="23213" class="Symbol">)</a> <a id="23215" class="Symbol">→</a> <a id="23217" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23206" class="Bound">m</a> <a id="23219" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23221" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23208" class="Bound">n</a> <a id="23223" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="23225" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23208" class="Bound">n</a> <a id="23227" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23229" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23206" class="Bound">m</a>
<a id="23231" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23193" class="Function">+-comm′</a> <a id="23239" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23239" class="Bound">m</a> <a id="23241" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="23246" class="Keyword">rewrite</a> <a id="23254" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#22968" class="Function">+-identity′</a> <a id="23266" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23239" class="Bound">m</a> <a id="23268" class="Symbol">=</a> <a id="23270" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="23275" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23193" class="Function">+-comm′</a> <a id="23283" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23283" class="Bound">m</a> <a id="23285" class="Symbol">(</a><a id="23286" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="23290" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23290" class="Bound">n</a><a id="23291" class="Symbol">)</a> <a id="23293" class="Keyword">rewrite</a> <a id="23301" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23081" class="Function">+-suc′</a> <a id="23308" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23283" class="Bound">m</a> <a id="23310" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23290" class="Bound">n</a> <a id="23312" class="Symbol">|</a> <a id="23314" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23193" class="Function">+-comm′</a> <a id="23322" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23283" class="Bound">m</a> <a id="23324" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#23290" class="Bound">n</a> <a id="23326" class="Symbol">=</a> <a id="23328" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.


## Building proofs interactively

It is instructive to see how to build the alternative proof of
associativity using the interactive features of Agda in Emacs.
Begin by typing:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = ?

The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `C-c C-l` (control-c
followed by control-l), the question mark will be replaced:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = { }0

The empty braces are called a _hole_, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text:

    ?0 : ((m + n) + p) ≡ (m + (n + p))

This indicates that hole 0 is to be filled in with a proof of
the stated judgment.

We wish to prove the proposition by induction on `m`.  Move
the cursor into the hole and type `C-c C-c`.  You will be given
the prompt:

    pattern variables to case (empty for split on result):

Typing `m` will cause a split on that variable, resulting
in an update to the code:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = { }0
    +-assoc′ (suc m) n p = { }1

There are now two holes, and the window at the bottom tells you what
each is required to prove:

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

Going into hole 0 and typing `C-c C-,` will display the text:

    Goal: (n + p) ≡ (n + p)
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ

This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `C-c C-r` will fill it in.
Typing `C-c C-l` renumbers the remaining hole to 0:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p = { }0

Going into the new hole 0 and typing `C-c C-,` will display the text:

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = { }0

Going into the remaining hole and typing `C-c C-,` will display the text:

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

The proof of the given goal is trivial, and going into the goal and
typing `C-c C-r` will fill it in, completing the proof:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


#### Exercise `+-swap` (recommended) {#plus-swap}

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.

{% raw %}<pre class="Agda"><a id="26868" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

{% raw %}<pre class="Agda"><a id="27093" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

{% raw %}<pre class="Agda"><a id="27294" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `*-comm` (practice) {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

{% raw %}<pre class="Agda"><a id="27562" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `0∸n≡0` (practice) {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

{% raw %}<pre class="Agda"><a id="27727" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `∸-|-assoc` (practice) {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

{% raw %}<pre class="Agda"><a id="27936" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `+*^` (stretch)

Show the following three laws

    m ^ (n + p) ≡ (m ^ n) * (m ^ p)
    (m * n) ^ p ≡ (m ^ p) * (n ^ p)
    m ^ (n * p) ≡ (m ^ n) ^ p

for all `m`, `n`, and `p`.


#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that
Exercise [Bin]({{ site.baseurl }}/Naturals/#Bin)
defines a datatype of bitstrings representing natural numbers
{% raw %}<pre class="Agda"><a id="28334" class="Keyword">data</a> <a id="Bin"></a><a id="28339" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28339" class="Datatype">Bin</a> <a id="28343" class="Symbol">:</a> <a id="28345" class="PrimitiveType">Set</a> <a id="28349" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="28357" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28357" class="InductiveConstructor">nil</a> <a id="28361" class="Symbol">:</a> <a id="28363" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28339" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="28369" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28369" class="InductiveConstructor Operator">x0_</a> <a id="28373" class="Symbol">:</a> <a id="28375" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28339" class="Datatype">Bin</a> <a id="28379" class="Symbol">→</a> <a id="28381" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28339" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="28387" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28387" class="InductiveConstructor Operator">x1_</a> <a id="28391" class="Symbol">:</a> <a id="28393" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28339" class="Datatype">Bin</a> <a id="28397" class="Symbol">→</a> <a id="28399" href="plfa.part1.https://agda.github.io/agda-stdlib/v1.1/Induction.html#28339" class="Datatype">Bin</a>
</pre>{% endraw %}and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings:

    from (inc x) ≡ suc (from x)
    to (from x) ≡ x
    from (to n) ≡ n

For each law: if it holds, prove; if not, give a counterexample.

{% raw %}<pre class="Agda"><a id="28733" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="28870" class="Keyword">import</a> <a id="28877" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="28897" class="Keyword">using</a> <a id="28903" class="Symbol">(</a><a id="28904" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="28911" class="Symbol">;</a> <a id="28913" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="28924" class="Symbol">;</a> <a id="28926" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="28931" class="Symbol">;</a> <a id="28933" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="28939" class="Symbol">)</a>
</pre>{% endraw %}
## Unicode

This chapter uses the following unicode:

    ∀  U+2200  FOR ALL (\forall, \all)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')

Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).
