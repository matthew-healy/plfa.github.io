---
src       : "src/plfa/part1/Relations.lagda.md"
title     : "Relations: Inductive definition of relations"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
---

{% raw %}<pre class="Agda"><a id="161" class="Keyword">module</a> <a id="168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}" class="Module">plfa.part1.Relations</a> <a id="189" class="Keyword">where</a>
</pre>{% endraw %}
After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.

## Imports

{% raw %}<pre class="Agda"><a id="354" class="Keyword">import</a> <a id="361" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="399" class="Symbol">as</a> <a id="402" class="Module">Eq</a>
<a id="405" class="Keyword">open</a> <a id="410" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="413" class="Keyword">using</a> <a id="419" class="Symbol">(</a><a id="420" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="423" class="Symbol">;</a> <a id="425" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="429" class="Symbol">;</a> <a id="431" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="435" class="Symbol">)</a>
<a id="437" class="Keyword">open</a> <a id="442" class="Keyword">import</a> <a id="449" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="458" class="Keyword">using</a> <a id="464" class="Symbol">(</a><a id="465" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="466" class="Symbol">;</a> <a id="468" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="472" class="Symbol">;</a> <a id="474" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="477" class="Symbol">;</a> <a id="479" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="482" class="Symbol">)</a>
<a id="484" class="Keyword">open</a> <a id="489" class="Keyword">import</a> <a id="496" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="516" class="Keyword">using</a> <a id="522" class="Symbol">(</a><a id="523" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="529" class="Symbol">;</a> <a id="531" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="542" class="Symbol">)</a>
</pre>{% endraw %}

## Defining relations

The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
{% raw %}<pre class="Agda"><a id="1203" class="Keyword">data</a> <a id="_≤_"></a><a id="1208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">_≤_</a> <a id="1212" class="Symbol">:</a> <a id="1214" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1216" class="Symbol">→</a> <a id="1218" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1220" class="Symbol">→</a> <a id="1222" class="PrimitiveType">Set</a> <a id="1226" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a> <a id="1239" class="Symbol">:</a> <a id="1241" class="Symbol">∀</a> <a id="1243" class="Symbol">{</a><a id="1244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1244" class="Bound">n</a> <a id="1246" class="Symbol">:</a> <a id="1248" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1249" class="Symbol">}</a>
      <a id="1257" class="Comment">--------</a>
    <a id="1270" class="Symbol">→</a> <a id="1272" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="1277" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="1279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1244" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="1288" class="Symbol">:</a> <a id="1290" class="Symbol">∀</a> <a id="1292" class="Symbol">{</a><a id="1293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1293" class="Bound">m</a> <a id="1295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1295" class="Bound">n</a> <a id="1297" class="Symbol">:</a> <a id="1299" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1300" class="Symbol">}</a>
    <a id="1306" class="Symbol">→</a> <a id="1308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1293" class="Bound">m</a> <a id="1310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="1312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1295" class="Bound">n</a>
      <a id="1320" class="Comment">-------------</a>
    <a id="1338" class="Symbol">→</a> <a id="1340" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1293" class="Bound">m</a> <a id="1346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="1348" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1295" class="Bound">n</a>
</pre>{% endraw %}Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.

Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`:

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof:
{% raw %}<pre class="Agda"><a id="2614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#2614" class="Function">_</a> <a id="2616" class="Symbol">:</a> <a id="2618" class="Number">2</a> <a id="2620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="2622" class="Number">4</a>
<a id="2624" class="Symbol">_</a> <a id="2626" class="Symbol">=</a> <a id="2628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="2632" class="Symbol">(</a><a id="2633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="2637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a><a id="2640" class="Symbol">)</a>
</pre>{% endraw %}



## Implicit arguments

This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit:
{% raw %}<pre class="Agda"><a id="3619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#3619" class="Function">_</a> <a id="3621" class="Symbol">:</a> <a id="3623" class="Number">2</a> <a id="3625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="3627" class="Number">4</a>
<a id="3629" class="Symbol">_</a> <a id="3631" class="Symbol">=</a> <a id="3633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="3637" class="Symbol">{</a><a id="3638" class="Number">1</a><a id="3639" class="Symbol">}</a> <a id="3641" class="Symbol">{</a><a id="3642" class="Number">3</a><a id="3643" class="Symbol">}</a> <a id="3645" class="Symbol">(</a><a id="3646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="3650" class="Symbol">{</a><a id="3651" class="Number">0</a><a id="3652" class="Symbol">}</a> <a id="3654" class="Symbol">{</a><a id="3655" class="Number">2</a><a id="3656" class="Symbol">}</a> <a id="3658" class="Symbol">(</a><a id="3659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a> <a id="3663" class="Symbol">{</a><a id="3664" class="Number">2</a><a id="3665" class="Symbol">}))</a>
</pre>{% endraw %}One may also identify implicit arguments by name:
{% raw %}<pre class="Agda"><a id="3727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#3727" class="Function">_</a> <a id="3729" class="Symbol">:</a> <a id="3731" class="Number">2</a> <a id="3733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="3735" class="Number">4</a>
<a id="3737" class="Symbol">_</a> <a id="3739" class="Symbol">=</a> <a id="3741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="3745" class="Symbol">{</a><a id="3746" class="Argument">m</a> <a id="3748" class="Symbol">=</a> <a id="3750" class="Number">1</a><a id="3751" class="Symbol">}</a> <a id="3753" class="Symbol">{</a><a id="3754" class="Argument">n</a> <a id="3756" class="Symbol">=</a> <a id="3758" class="Number">3</a><a id="3759" class="Symbol">}</a> <a id="3761" class="Symbol">(</a><a id="3762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="3766" class="Symbol">{</a><a id="3767" class="Argument">m</a> <a id="3769" class="Symbol">=</a> <a id="3771" class="Number">0</a><a id="3772" class="Symbol">}</a> <a id="3774" class="Symbol">{</a><a id="3775" class="Argument">n</a> <a id="3777" class="Symbol">=</a> <a id="3779" class="Number">2</a><a id="3780" class="Symbol">}</a> <a id="3782" class="Symbol">(</a><a id="3783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a> <a id="3787" class="Symbol">{</a><a id="3788" class="Argument">n</a> <a id="3790" class="Symbol">=</a> <a id="3792" class="Number">2</a><a id="3793" class="Symbol">}))</a>
</pre>{% endraw %}In the latter format, you can choose to only supply some implicit arguments:
{% raw %}<pre class="Agda"><a id="3882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#3882" class="Function">_</a> <a id="3884" class="Symbol">:</a> <a id="3886" class="Number">2</a> <a id="3888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="3890" class="Number">4</a>
<a id="3892" class="Symbol">_</a> <a id="3894" class="Symbol">=</a> <a id="3896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="3900" class="Symbol">{</a><a id="3901" class="Argument">n</a> <a id="3903" class="Symbol">=</a> <a id="3905" class="Number">3</a><a id="3906" class="Symbol">}</a> <a id="3908" class="Symbol">(</a><a id="3909" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="3913" class="Symbol">{</a><a id="3914" class="Argument">n</a> <a id="3916" class="Symbol">=</a> <a id="3918" class="Number">2</a><a id="3919" class="Symbol">}</a> <a id="3921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a><a id="3924" class="Symbol">)</a>
</pre>{% endraw %}It is not permitted to swap implicit arguments, even when named.

We can ask Agda to use the same inference to try and infer an _explicit_ term,
by writing `_`. For instance, we can define a variant of the proposition
`+-identityʳ` with implicit arguments:
{% raw %}<pre class="Agda"><a id="+-identityʳ′"></a><a id="4191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#4191" class="Function">+-identityʳ′</a> <a id="4204" class="Symbol">:</a> <a id="4206" class="Symbol">∀</a> <a id="4208" class="Symbol">{</a><a id="4209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#4209" class="Bound">m</a> <a id="4211" class="Symbol">:</a> <a id="4213" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="4214" class="Symbol">}</a> <a id="4216" class="Symbol">→</a> <a id="4218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#4209" class="Bound">m</a> <a id="4220" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="4222" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="4227" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="4229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#4209" class="Bound">m</a>
<a id="4231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#4191" class="Function">+-identityʳ′</a> <a id="4244" class="Symbol">=</a> <a id="4246" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a> <a id="4258" class="Symbol">_</a>
</pre>{% endraw %}We use `_` to ask Agda to infer the value of the _explicit_ argument from
context. There is only one value which gives us the correct proof, `m`, so Agda
happily fills it in.
If Agda fails to infer the value, it reports an error.


## Precedence

We declare the precedence for comparison as follows:
{% raw %}<pre class="Agda"><a id="4568" class="Keyword">infix</a> <a id="4574" class="Number">4</a> <a id="4576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">_≤_</a>
</pre>{% endraw %}We set the precedence of `_≤_` at level 4, so it binds less tightly
than `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable]({{ site.baseurl }}/Decidable/).


## Inversion

In our definitions, we go from smaller things to larger things.
For instance, from `m ≤ n` we can conclude `suc m ≤ suc n`,
where `suc m` is bigger than `m` (that is, the former contains
the latter), and `suc n` is bigger than `n`. But sometimes we
want to go from bigger things to smaller things.

There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  This lets us invert our previous rule.
{% raw %}<pre class="Agda"><a id="inv-s≤s"></a><a id="5594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5594" class="Function">inv-s≤s</a> <a id="5602" class="Symbol">:</a> <a id="5604" class="Symbol">∀</a> <a id="5606" class="Symbol">{</a><a id="5607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5607" class="Bound">m</a> <a id="5609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5609" class="Bound">n</a> <a id="5611" class="Symbol">:</a> <a id="5613" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="5614" class="Symbol">}</a>
  <a id="5618" class="Symbol">→</a> <a id="5620" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="5624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5607" class="Bound">m</a> <a id="5626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="5628" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="5632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5609" class="Bound">n</a>
    <a id="5638" class="Comment">-------------</a>
  <a id="5654" class="Symbol">→</a> <a id="5656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5607" class="Bound">m</a> <a id="5658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="5660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5609" class="Bound">n</a>
<a id="5662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5594" class="Function">inv-s≤s</a> <a id="5670" class="Symbol">(</a><a id="5671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="5675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5675" class="Bound">m≤n</a><a id="5678" class="Symbol">)</a> <a id="5680" class="Symbol">=</a> <a id="5682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#5675" class="Bound">m≤n</a>
</pre>{% endraw %}Here `m≤n` (with no spaces) is a variable name while
`m ≤ n` (with spaces) is a type, and the latter
is the type of the former.  It is a common convention
in Agda to derive a variable name by removing
spaces from its type.

Not every rule is invertible; indeed, the rule for `z≤n` has
no non-implicit hypotheses, so there is nothing to invert.
But often inversions of this kind hold.

Another example of inversion is showing that there is
only one way a number can be less than or equal to zero.
{% raw %}<pre class="Agda"><a id="inv-z≤n"></a><a id="6190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#6190" class="Function">inv-z≤n</a> <a id="6198" class="Symbol">:</a> <a id="6200" class="Symbol">∀</a> <a id="6202" class="Symbol">{</a><a id="6203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#6203" class="Bound">m</a> <a id="6205" class="Symbol">:</a> <a id="6207" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="6208" class="Symbol">}</a>
  <a id="6212" class="Symbol">→</a> <a id="6214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#6203" class="Bound">m</a> <a id="6216" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="6218" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
    <a id="6227" class="Comment">--------</a>
  <a id="6238" class="Symbol">→</a> <a id="6240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#6203" class="Bound">m</a> <a id="6242" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="6244" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
<a id="6249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#6190" class="Function">inv-z≤n</a> <a id="6257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a> <a id="6261" class="Symbol">=</a> <a id="6263" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
## Properties of ordering relations

Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
partial order but not a total order.


#### Exercise `orderings` (practice) {#orderings}

Give an example of a preorder that is not a partial order.

{% raw %}<pre class="Agda"><a id="7765" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
Give an example of a partial order that is not a total order.

{% raw %}<pre class="Agda"><a id="7860" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
{% raw %}<pre class="Agda"><a id="≤-refl"></a><a id="8160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8160" class="Function">≤-refl</a> <a id="8167" class="Symbol">:</a> <a id="8169" class="Symbol">∀</a> <a id="8171" class="Symbol">{</a><a id="8172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8172" class="Bound">n</a> <a id="8174" class="Symbol">:</a> <a id="8176" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8177" class="Symbol">}</a>
    <a id="8183" class="Comment">-----</a>
  <a id="8191" class="Symbol">→</a> <a id="8193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8172" class="Bound">n</a> <a id="8195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="8197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8172" class="Bound">n</a>
<a id="8199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8160" class="Function">≤-refl</a> <a id="8206" class="Symbol">{</a><a id="8207" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="8211" class="Symbol">}</a> <a id="8213" class="Symbol">=</a> <a id="8215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a>
<a id="8219" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8160" class="Function">≤-refl</a> <a id="8226" class="Symbol">{</a><a id="8227" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="8231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8231" class="Bound">n</a><a id="8232" class="Symbol">}</a> <a id="8234" class="Symbol">=</a> <a id="8236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="8240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8160" class="Function">≤-refl</a>
</pre>{% endraw %}The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
{% raw %}<pre class="Agda"><a id="≤-trans"></a><a id="8877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8877" class="Function">≤-trans</a> <a id="8885" class="Symbol">:</a> <a id="8887" class="Symbol">∀</a> <a id="8889" class="Symbol">{</a><a id="8890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8890" class="Bound">m</a> <a id="8892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8892" class="Bound">n</a> <a id="8894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8894" class="Bound">p</a> <a id="8896" class="Symbol">:</a> <a id="8898" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8899" class="Symbol">}</a>
  <a id="8903" class="Symbol">→</a> <a id="8905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8890" class="Bound">m</a> <a id="8907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="8909" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8892" class="Bound">n</a>
  <a id="8913" class="Symbol">→</a> <a id="8915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8892" class="Bound">n</a> <a id="8917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="8919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8894" class="Bound">p</a>
    <a id="8925" class="Comment">-----</a>
  <a id="8933" class="Symbol">→</a> <a id="8935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8890" class="Bound">m</a> <a id="8937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="8939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8894" class="Bound">p</a>
<a id="8941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8877" class="Function">≤-trans</a> <a id="8949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a>       <a id="8959" class="Symbol">_</a>          <a id="8970" class="Symbol">=</a>  <a id="8973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a>
<a id="8977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8877" class="Function">≤-trans</a> <a id="8985" class="Symbol">(</a><a id="8986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="8990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8990" class="Bound">m≤n</a><a id="8993" class="Symbol">)</a> <a id="8995" class="Symbol">(</a><a id="8996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="9000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9000" class="Bound">n≤p</a><a id="9003" class="Symbol">)</a>  <a id="9006" class="Symbol">=</a>  <a id="9009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="9013" class="Symbol">(</a><a id="9014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8877" class="Function">≤-trans</a> <a id="9022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8990" class="Bound">m≤n</a> <a id="9026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9000" class="Bound">n≤p</a><a id="9029" class="Symbol">)</a>
</pre>{% endraw %}Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤ p`,
which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.

Alternatively, we could make the implicit parameters explicit:
{% raw %}<pre class="Agda"><a id="≤-trans′"></a><a id="9990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9990" class="Function">≤-trans′</a> <a id="9999" class="Symbol">:</a> <a id="10001" class="Symbol">∀</a> <a id="10003" class="Symbol">(</a><a id="10004" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10004" class="Bound">m</a> <a id="10006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10006" class="Bound">n</a> <a id="10008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10008" class="Bound">p</a> <a id="10010" class="Symbol">:</a> <a id="10012" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10013" class="Symbol">)</a>
  <a id="10017" class="Symbol">→</a> <a id="10019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10004" class="Bound">m</a> <a id="10021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="10023" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10006" class="Bound">n</a>
  <a id="10027" class="Symbol">→</a> <a id="10029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10006" class="Bound">n</a> <a id="10031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="10033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10008" class="Bound">p</a>
    <a id="10039" class="Comment">-----</a>
  <a id="10047" class="Symbol">→</a> <a id="10049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10004" class="Bound">m</a> <a id="10051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="10053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10008" class="Bound">p</a>
<a id="10055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9990" class="Function">≤-trans′</a> <a id="10064" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="10072" class="Symbol">_</a>       <a id="10080" class="Symbol">_</a>       <a id="10088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a>       <a id="10098" class="Symbol">_</a>          <a id="10109" class="Symbol">=</a>  <a id="10112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a>
<a id="10116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9990" class="Function">≤-trans′</a> <a id="10125" class="Symbol">(</a><a id="10126" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10130" class="Bound">m</a><a id="10131" class="Symbol">)</a> <a id="10133" class="Symbol">(</a><a id="10134" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10138" class="Bound">n</a><a id="10139" class="Symbol">)</a> <a id="10141" class="Symbol">(</a><a id="10142" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="10146" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10146" class="Bound">p</a><a id="10147" class="Symbol">)</a> <a id="10149" class="Symbol">(</a><a id="10150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="10154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10154" class="Bound">m≤n</a><a id="10157" class="Symbol">)</a> <a id="10159" class="Symbol">(</a><a id="10160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="10164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10164" class="Bound">n≤p</a><a id="10167" class="Symbol">)</a>  <a id="10170" class="Symbol">=</a>  <a id="10173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="10177" class="Symbol">(</a><a id="10178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#9990" class="Function">≤-trans′</a> <a id="10187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10130" class="Bound">m</a> <a id="10189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10138" class="Bound">n</a> <a id="10191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10146" class="Bound">p</a> <a id="10193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10154" class="Bound">m≤n</a> <a id="10197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10164" class="Bound">n≤p</a><a id="10200" class="Symbol">)</a>
</pre>{% endraw %}One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Anti-symmetry

The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and `n ≤
m` hold, then `m ≡ n` holds:
{% raw %}<pre class="Agda"><a id="≤-antisym"></a><a id="10945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10945" class="Function">≤-antisym</a> <a id="10955" class="Symbol">:</a> <a id="10957" class="Symbol">∀</a> <a id="10959" class="Symbol">{</a><a id="10960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10960" class="Bound">m</a> <a id="10962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10962" class="Bound">n</a> <a id="10964" class="Symbol">:</a> <a id="10966" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="10967" class="Symbol">}</a>
  <a id="10971" class="Symbol">→</a> <a id="10973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10960" class="Bound">m</a> <a id="10975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="10977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10962" class="Bound">n</a>
  <a id="10981" class="Symbol">→</a> <a id="10983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10962" class="Bound">n</a> <a id="10985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="10987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10960" class="Bound">m</a>
    <a id="10993" class="Comment">-----</a>
  <a id="11001" class="Symbol">→</a> <a id="11003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10960" class="Bound">m</a> <a id="11005" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="11007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10962" class="Bound">n</a>
<a id="11009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10945" class="Function">≤-antisym</a> <a id="11019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a>       <a id="11029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a>        <a id="11040" class="Symbol">=</a>  <a id="11043" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="11048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10945" class="Function">≤-antisym</a> <a id="11058" class="Symbol">(</a><a id="11059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="11063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11063" class="Bound">m≤n</a><a id="11066" class="Symbol">)</a> <a id="11068" class="Symbol">(</a><a id="11069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="11073" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11073" class="Bound">n≤m</a><a id="11076" class="Symbol">)</a>  <a id="11079" class="Symbol">=</a>  <a id="11082" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="11087" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11091" class="Symbol">(</a><a id="11092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#10945" class="Function">≤-antisym</a> <a id="11102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11063" class="Bound">m≤n</a> <a id="11106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#11073" class="Bound">n≤m</a><a id="11109" class="Symbol">)</a>
</pre>{% endraw %}Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.

In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.

#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

{% raw %}<pre class="Agda"><a id="11915" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total:
{% raw %}<pre class="Agda"><a id="12169" class="Keyword">data</a> <a id="Total"></a><a id="12174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12174" class="Datatype">Total</a> <a id="12180" class="Symbol">(</a><a id="12181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12181" class="Bound">m</a> <a id="12183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12183" class="Bound">n</a> <a id="12185" class="Symbol">:</a> <a id="12187" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12188" class="Symbol">)</a> <a id="12190" class="Symbol">:</a> <a id="12192" class="PrimitiveType">Set</a> <a id="12196" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="12205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12205" class="InductiveConstructor">forward</a> <a id="12213" class="Symbol">:</a>
      <a id="12221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12181" class="Bound">m</a> <a id="12223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="12225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12183" class="Bound">n</a>
      <a id="12233" class="Comment">---------</a>
    <a id="12247" class="Symbol">→</a> <a id="12249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12174" class="Datatype">Total</a> <a id="12255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12181" class="Bound">m</a> <a id="12257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12183" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="12262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12262" class="InductiveConstructor">flipped</a> <a id="12270" class="Symbol">:</a>
      <a id="12278" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12183" class="Bound">n</a> <a id="12280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="12282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12181" class="Bound">m</a>
      <a id="12290" class="Comment">---------</a>
    <a id="12304" class="Symbol">→</a> <a id="12306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12174" class="Datatype">Total</a> <a id="12312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12181" class="Bound">m</a> <a id="12314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12183" class="Bound">n</a>
</pre>{% endraw %}Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives]({{ site.baseurl }}/Connectives/).)

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
{% raw %}<pre class="Agda"><a id="12803" class="Keyword">data</a> <a id="Total′"></a><a id="12808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12808" class="Datatype">Total′</a> <a id="12815" class="Symbol">:</a> <a id="12817" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="12819" class="Symbol">→</a> <a id="12821" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="12823" class="Symbol">→</a> <a id="12825" class="PrimitiveType">Set</a> <a id="12829" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="12838" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12838" class="InductiveConstructor">forward′</a> <a id="12847" class="Symbol">:</a> <a id="12849" class="Symbol">∀</a> <a id="12851" class="Symbol">{</a><a id="12852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12852" class="Bound">m</a> <a id="12854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12854" class="Bound">n</a> <a id="12856" class="Symbol">:</a> <a id="12858" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12859" class="Symbol">}</a>
    <a id="12865" class="Symbol">→</a> <a id="12867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12852" class="Bound">m</a> <a id="12869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="12871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12854" class="Bound">n</a>
      <a id="12879" class="Comment">----------</a>
    <a id="12894" class="Symbol">→</a> <a id="12896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12808" class="Datatype">Total′</a> <a id="12903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12852" class="Bound">m</a> <a id="12905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12854" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="12910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12910" class="InductiveConstructor">flipped′</a> <a id="12919" class="Symbol">:</a> <a id="12921" class="Symbol">∀</a> <a id="12923" class="Symbol">{</a><a id="12924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12924" class="Bound">m</a> <a id="12926" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12926" class="Bound">n</a> <a id="12928" class="Symbol">:</a> <a id="12930" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12931" class="Symbol">}</a>
    <a id="12937" class="Symbol">→</a> <a id="12939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12926" class="Bound">n</a> <a id="12941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="12943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12924" class="Bound">m</a>
      <a id="12951" class="Comment">----------</a>
    <a id="12966" class="Symbol">→</a> <a id="12968" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12808" class="Datatype">Total′</a> <a id="12975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12924" class="Bound">m</a> <a id="12977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12926" class="Bound">n</a>
</pre>{% endraw %}Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality:
{% raw %}<pre class="Agda"><a id="≤-total"></a><a id="13496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13496" class="Function">≤-total</a> <a id="13504" class="Symbol">:</a> <a id="13506" class="Symbol">∀</a> <a id="13508" class="Symbol">(</a><a id="13509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13509" class="Bound">m</a> <a id="13511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13511" class="Bound">n</a> <a id="13513" class="Symbol">:</a> <a id="13515" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="13516" class="Symbol">)</a> <a id="13518" class="Symbol">→</a> <a id="13520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12174" class="Datatype">Total</a> <a id="13526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13509" class="Bound">m</a> <a id="13528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13511" class="Bound">n</a>
<a id="13530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13496" class="Function">≤-total</a> <a id="13538" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="13546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13546" class="Bound">n</a>                         <a id="13572" class="Symbol">=</a>  <a id="13575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12205" class="InductiveConstructor">forward</a> <a id="13583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a>
<a id="13587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13496" class="Function">≤-total</a> <a id="13595" class="Symbol">(</a><a id="13596" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13600" class="Bound">m</a><a id="13601" class="Symbol">)</a> <a id="13603" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="13629" class="Symbol">=</a>  <a id="13632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12262" class="InductiveConstructor">flipped</a> <a id="13640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a>
<a id="13644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13496" class="Function">≤-total</a> <a id="13652" class="Symbol">(</a><a id="13653" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13657" class="Bound">m</a><a id="13658" class="Symbol">)</a> <a id="13660" class="Symbol">(</a><a id="13661" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13665" class="Bound">n</a><a id="13666" class="Symbol">)</a> <a id="13668" class="Keyword">with</a> <a id="13673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13496" class="Function">≤-total</a> <a id="13681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13657" class="Bound">m</a> <a id="13683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13665" class="Bound">n</a>
<a id="13685" class="Symbol">...</a>                        <a id="13712" class="Symbol">|</a> <a id="13714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12205" class="InductiveConstructor">forward</a> <a id="13722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13722" class="Bound">m≤n</a>  <a id="13727" class="Symbol">=</a>  <a id="13730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12205" class="InductiveConstructor">forward</a> <a id="13738" class="Symbol">(</a><a id="13739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="13743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13722" class="Bound">m≤n</a><a id="13746" class="Symbol">)</a>
<a id="13748" class="Symbol">...</a>                        <a id="13775" class="Symbol">|</a> <a id="13777" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12262" class="InductiveConstructor">flipped</a> <a id="13785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13785" class="Bound">n≤m</a>  <a id="13790" class="Symbol">=</a>  <a id="13793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12262" class="InductiveConstructor">flipped</a> <a id="13801" class="Symbol">(</a><a id="13802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="13806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#13785" class="Bound">n≤m</a><a id="13809" class="Symbol">)</a>
</pre>{% endraw %}In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
{% raw %}<pre class="Agda"><a id="≤-total′"></a><a id="15301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15301" class="Function">≤-total′</a> <a id="15310" class="Symbol">:</a> <a id="15312" class="Symbol">∀</a> <a id="15314" class="Symbol">(</a><a id="15315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15315" class="Bound">m</a> <a id="15317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15317" class="Bound">n</a> <a id="15319" class="Symbol">:</a> <a id="15321" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="15322" class="Symbol">)</a> <a id="15324" class="Symbol">→</a> <a id="15326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12174" class="Datatype">Total</a> <a id="15332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15315" class="Bound">m</a> <a id="15334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15317" class="Bound">n</a>
<a id="15336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15301" class="Function">≤-total′</a> <a id="15345" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="15353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15353" class="Bound">n</a>        <a id="15362" class="Symbol">=</a>  <a id="15365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12205" class="InductiveConstructor">forward</a> <a id="15373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a>
<a id="15377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15301" class="Function">≤-total′</a> <a id="15386" class="Symbol">(</a><a id="15387" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15391" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15391" class="Bound">m</a><a id="15392" class="Symbol">)</a> <a id="15394" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>     <a id="15403" class="Symbol">=</a>  <a id="15406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12262" class="InductiveConstructor">flipped</a> <a id="15414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a>
<a id="15418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15301" class="Function">≤-total′</a> <a id="15427" class="Symbol">(</a><a id="15428" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15432" class="Bound">m</a><a id="15433" class="Symbol">)</a> <a id="15435" class="Symbol">(</a><a id="15436" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15440" class="Bound">n</a><a id="15441" class="Symbol">)</a>  <a id="15444" class="Symbol">=</a>  <a id="15447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15479" class="Function">helper</a> <a id="15454" class="Symbol">(</a><a id="15455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15301" class="Function">≤-total′</a> <a id="15464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15432" class="Bound">m</a> <a id="15466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15440" class="Bound">n</a><a id="15467" class="Symbol">)</a>
  <a id="15471" class="Keyword">where</a>
  <a id="15479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15479" class="Function">helper</a> <a id="15486" class="Symbol">:</a> <a id="15488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12174" class="Datatype">Total</a> <a id="15494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15432" class="Bound">m</a> <a id="15496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15440" class="Bound">n</a> <a id="15498" class="Symbol">→</a> <a id="15500" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12174" class="Datatype">Total</a> <a id="15506" class="Symbol">(</a><a id="15507" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15432" class="Bound">m</a><a id="15512" class="Symbol">)</a> <a id="15514" class="Symbol">(</a><a id="15515" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15440" class="Bound">n</a><a id="15520" class="Symbol">)</a>
  <a id="15524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15479" class="Function">helper</a> <a id="15531" class="Symbol">(</a><a id="15532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12205" class="InductiveConstructor">forward</a> <a id="15540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15540" class="Bound">m≤n</a><a id="15543" class="Symbol">)</a>  <a id="15546" class="Symbol">=</a>  <a id="15549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12205" class="InductiveConstructor">forward</a> <a id="15557" class="Symbol">(</a><a id="15558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="15562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15540" class="Bound">m≤n</a><a id="15565" class="Symbol">)</a>
  <a id="15569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15479" class="Function">helper</a> <a id="15576" class="Symbol">(</a><a id="15577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12262" class="InductiveConstructor">flipped</a> <a id="15585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15585" class="Bound">n≤m</a><a id="15588" class="Symbol">)</a>  <a id="15591" class="Symbol">=</a>  <a id="15594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12262" class="InductiveConstructor">flipped</a> <a id="15602" class="Symbol">(</a><a id="15603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="15607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#15585" class="Bound">n≤m</a><a id="15610" class="Symbol">)</a>
</pre>{% endraw %}This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
{% raw %}<pre class="Agda"><a id="≤-total″"></a><a id="16232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16232" class="Function">≤-total″</a> <a id="16241" class="Symbol">:</a> <a id="16243" class="Symbol">∀</a> <a id="16245" class="Symbol">(</a><a id="16246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16246" class="Bound">m</a> <a id="16248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16248" class="Bound">n</a> <a id="16250" class="Symbol">:</a> <a id="16252" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="16253" class="Symbol">)</a> <a id="16255" class="Symbol">→</a> <a id="16257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12174" class="Datatype">Total</a> <a id="16263" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16246" class="Bound">m</a> <a id="16265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16248" class="Bound">n</a>
<a id="16267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16232" class="Function">≤-total″</a> <a id="16276" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16276" class="Bound">m</a>       <a id="16284" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="16310" class="Symbol">=</a>  <a id="16313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12262" class="InductiveConstructor">flipped</a> <a id="16321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a>
<a id="16325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16232" class="Function">≤-total″</a> <a id="16334" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="16342" class="Symbol">(</a><a id="16343" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16347" class="Bound">n</a><a id="16348" class="Symbol">)</a>                   <a id="16368" class="Symbol">=</a>  <a id="16371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12205" class="InductiveConstructor">forward</a> <a id="16379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1235" class="InductiveConstructor">z≤n</a>
<a id="16383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16232" class="Function">≤-total″</a> <a id="16392" class="Symbol">(</a><a id="16393" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16397" class="Bound">m</a><a id="16398" class="Symbol">)</a> <a id="16400" class="Symbol">(</a><a id="16401" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="16405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16405" class="Bound">n</a><a id="16406" class="Symbol">)</a> <a id="16408" class="Keyword">with</a> <a id="16413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16232" class="Function">≤-total″</a> <a id="16422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16397" class="Bound">m</a> <a id="16424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16405" class="Bound">n</a>
<a id="16426" class="Symbol">...</a>                        <a id="16453" class="Symbol">|</a> <a id="16455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12205" class="InductiveConstructor">forward</a> <a id="16463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16463" class="Bound">m≤n</a>   <a id="16469" class="Symbol">=</a>  <a id="16472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12205" class="InductiveConstructor">forward</a> <a id="16480" class="Symbol">(</a><a id="16481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="16485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16463" class="Bound">m≤n</a><a id="16488" class="Symbol">)</a>
<a id="16490" class="Symbol">...</a>                        <a id="16517" class="Symbol">|</a> <a id="16519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12262" class="InductiveConstructor">flipped</a> <a id="16527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16527" class="Bound">n≤m</a>   <a id="16533" class="Symbol">=</a>  <a id="16536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#12262" class="InductiveConstructor">flipped</a> <a id="16544" class="Symbol">(</a><a id="16545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="16549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#16527" class="Bound">n≤m</a><a id="16552" class="Symbol">)</a>
</pre>{% endraw %}It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
{% raw %}<pre class="Agda"><a id="+-monoʳ-≤"></a><a id="17141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17141" class="Function">+-monoʳ-≤</a> <a id="17151" class="Symbol">:</a> <a id="17153" class="Symbol">∀</a> <a id="17155" class="Symbol">(</a><a id="17156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17156" class="Bound">n</a> <a id="17158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17158" class="Bound">p</a> <a id="17160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17160" class="Bound">q</a> <a id="17162" class="Symbol">:</a> <a id="17164" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17165" class="Symbol">)</a>
  <a id="17169" class="Symbol">→</a> <a id="17171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17158" class="Bound">p</a> <a id="17173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="17175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17160" class="Bound">q</a>
    <a id="17181" class="Comment">-------------</a>
  <a id="17197" class="Symbol">→</a> <a id="17199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17156" class="Bound">n</a> <a id="17201" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17158" class="Bound">p</a> <a id="17205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="17207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17156" class="Bound">n</a> <a id="17209" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="17211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17160" class="Bound">q</a>
<a id="17213" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17141" class="Function">+-monoʳ-≤</a> <a id="17223" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="17231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17231" class="Bound">p</a> <a id="17233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17233" class="Bound">q</a> <a id="17235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17235" class="Bound">p≤q</a>  <a id="17240" class="Symbol">=</a>  <a id="17243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17235" class="Bound">p≤q</a>
<a id="17247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17141" class="Function">+-monoʳ-≤</a> <a id="17257" class="Symbol">(</a><a id="17258" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="17262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17262" class="Bound">n</a><a id="17263" class="Symbol">)</a> <a id="17265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17265" class="Bound">p</a> <a id="17267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17267" class="Bound">q</a> <a id="17269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17269" class="Bound">p≤q</a>  <a id="17274" class="Symbol">=</a>  <a id="17277" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1284" class="InductiveConstructor">s≤s</a> <a id="17281" class="Symbol">(</a><a id="17282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17141" class="Function">+-monoʳ-≤</a> <a id="17292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17262" class="Bound">n</a> <a id="17294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17265" class="Bound">p</a> <a id="17296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17267" class="Bound">q</a> <a id="17298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17269" class="Bound">p≤q</a><a id="17301" class="Symbol">)</a>
</pre>{% endraw %}The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc n`, in which case
  `suc n + p ≤ suc n + q` simplifies to `suc (n + p) ≤ suc (n + q)`.
  The inductive hypothesis `+-monoʳ-≤ n p q p≤q` establishes that
  `n + p ≤ n + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
{% raw %}<pre class="Agda"><a id="+-monoˡ-≤"></a><a id="17941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17941" class="Function">+-monoˡ-≤</a> <a id="17951" class="Symbol">:</a> <a id="17953" class="Symbol">∀</a> <a id="17955" class="Symbol">(</a><a id="17956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17956" class="Bound">m</a> <a id="17958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17958" class="Bound">n</a> <a id="17960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17960" class="Bound">p</a> <a id="17962" class="Symbol">:</a> <a id="17964" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17965" class="Symbol">)</a>
  <a id="17969" class="Symbol">→</a> <a id="17971" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17956" class="Bound">m</a> <a id="17973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="17975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17958" class="Bound">n</a>
    <a id="17981" class="Comment">-------------</a>
  <a id="17997" class="Symbol">→</a> <a id="17999" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17956" class="Bound">m</a> <a id="18001" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17960" class="Bound">p</a> <a id="18005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="18007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17958" class="Bound">n</a> <a id="18009" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17960" class="Bound">p</a>
<a id="18013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17941" class="Function">+-monoˡ-≤</a> <a id="18023" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18023" class="Bound">m</a> <a id="18025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18025" class="Bound">n</a> <a id="18027" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18027" class="Bound">p</a> <a id="18029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18029" class="Bound">m≤n</a>  <a id="18034" class="Keyword">rewrite</a> <a id="18042" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="18049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18023" class="Bound">m</a> <a id="18051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18027" class="Bound">p</a> <a id="18053" class="Symbol">|</a> <a id="18055" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="18062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18025" class="Bound">n</a> <a id="18064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18027" class="Bound">p</a>  <a id="18067" class="Symbol">=</a> <a id="18069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17141" class="Function">+-monoʳ-≤</a> <a id="18079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18027" class="Bound">p</a> <a id="18081" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18023" class="Bound">m</a> <a id="18083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18025" class="Bound">n</a> <a id="18085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18029" class="Bound">m≤n</a>
</pre>{% endraw %}Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results:
{% raw %}<pre class="Agda"><a id="+-mono-≤"></a><a id="18283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18283" class="Function">+-mono-≤</a> <a id="18292" class="Symbol">:</a> <a id="18294" class="Symbol">∀</a> <a id="18296" class="Symbol">(</a><a id="18297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18297" class="Bound">m</a> <a id="18299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18299" class="Bound">n</a> <a id="18301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18301" class="Bound">p</a> <a id="18303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18303" class="Bound">q</a> <a id="18305" class="Symbol">:</a> <a id="18307" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18308" class="Symbol">)</a>
  <a id="18312" class="Symbol">→</a> <a id="18314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18297" class="Bound">m</a> <a id="18316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="18318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18299" class="Bound">n</a>
  <a id="18322" class="Symbol">→</a> <a id="18324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18301" class="Bound">p</a> <a id="18326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="18328" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18303" class="Bound">q</a>
    <a id="18334" class="Comment">-------------</a>
  <a id="18350" class="Symbol">→</a> <a id="18352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18297" class="Bound">m</a> <a id="18354" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18301" class="Bound">p</a> <a id="18358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#1208" class="Datatype Operator">≤</a> <a id="18360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18299" class="Bound">n</a> <a id="18362" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="18364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18303" class="Bound">q</a>
<a id="18366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18283" class="Function">+-mono-≤</a> <a id="18375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18375" class="Bound">m</a> <a id="18377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18377" class="Bound">n</a> <a id="18379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18379" class="Bound">p</a> <a id="18381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18381" class="Bound">q</a> <a id="18383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18383" class="Bound">m≤n</a> <a id="18387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18387" class="Bound">p≤q</a>  <a id="18392" class="Symbol">=</a>  <a id="18395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#8877" class="Function">≤-trans</a> <a id="18403" class="Symbol">(</a><a id="18404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17941" class="Function">+-monoˡ-≤</a> <a id="18414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18375" class="Bound">m</a> <a id="18416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18377" class="Bound">n</a> <a id="18418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18379" class="Bound">p</a> <a id="18420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18383" class="Bound">m≤n</a><a id="18423" class="Symbol">)</a> <a id="18425" class="Symbol">(</a><a id="18426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#17141" class="Function">+-monoʳ-≤</a> <a id="18436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18377" class="Bound">n</a> <a id="18438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18379" class="Bound">p</a> <a id="18440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18381" class="Bound">q</a> <a id="18442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18387" class="Bound">p≤q</a><a id="18445" class="Symbol">)</a>
</pre>{% endraw %}Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

{% raw %}<pre class="Agda"><a id="18754" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality:
{% raw %}<pre class="Agda"><a id="18887" class="Keyword">infix</a> <a id="18893" class="Number">4</a> <a id="18895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18905" class="Datatype Operator">_&lt;_</a>

<a id="18900" class="Keyword">data</a> <a id="_&lt;_"></a><a id="18905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18905" class="Datatype Operator">_&lt;_</a> <a id="18909" class="Symbol">:</a> <a id="18911" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="18913" class="Symbol">→</a> <a id="18915" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="18917" class="Symbol">→</a> <a id="18919" class="PrimitiveType">Set</a> <a id="18923" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="18932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18932" class="InductiveConstructor">z&lt;s</a> <a id="18936" class="Symbol">:</a> <a id="18938" class="Symbol">∀</a> <a id="18940" class="Symbol">{</a><a id="18941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18941" class="Bound">n</a> <a id="18943" class="Symbol">:</a> <a id="18945" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18946" class="Symbol">}</a>
      <a id="18954" class="Comment">------------</a>
    <a id="18971" class="Symbol">→</a> <a id="18973" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="18978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18905" class="Datatype Operator">&lt;</a> <a id="18980" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="18984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18941" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="18989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18989" class="InductiveConstructor">s&lt;s</a> <a id="18993" class="Symbol">:</a> <a id="18995" class="Symbol">∀</a> <a id="18997" class="Symbol">{</a><a id="18998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18998" class="Bound">m</a> <a id="19000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#19000" class="Bound">n</a> <a id="19002" class="Symbol">:</a> <a id="19004" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="19005" class="Symbol">}</a>
    <a id="19011" class="Symbol">→</a> <a id="19013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18998" class="Bound">m</a> <a id="19015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18905" class="Datatype Operator">&lt;</a> <a id="19017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#19000" class="Bound">n</a>
      <a id="19025" class="Comment">-------------</a>
    <a id="19043" class="Symbol">→</a> <a id="19045" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="19049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18998" class="Bound">m</a> <a id="19051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#18905" class="Datatype Operator">&lt;</a> <a id="19053" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="19057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#19000" class="Bound">n</a>
</pre>{% endraw %}The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation]({{ site.baseurl }}/Negation/).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

{% raw %}<pre class="Agda"><a id="20226" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `trichotomy` (practice) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation]({{ site.baseurl }}/Negation/).)

{% raw %}<pre class="Agda"><a id="20725" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `+-mono-<` (practice) {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

{% raw %}<pre class="Agda"><a id="20945" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

{% raw %}<pre class="Agda"><a id="21088" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.

{% raw %}<pre class="Agda"><a id="21359" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
{% raw %}<pre class="Agda"><a id="21598" class="Keyword">data</a> <a id="even"></a><a id="21603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21603" class="Datatype">even</a> <a id="21608" class="Symbol">:</a> <a id="21610" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="21612" class="Symbol">→</a> <a id="21614" class="PrimitiveType">Set</a>
<a id="21618" class="Keyword">data</a> <a id="odd"></a><a id="21623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21623" class="Datatype">odd</a>  <a id="21628" class="Symbol">:</a> <a id="21630" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="21632" class="Symbol">→</a> <a id="21634" class="PrimitiveType">Set</a>

<a id="21639" class="Keyword">data</a> <a id="21644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21603" class="Datatype">even</a> <a id="21649" class="Keyword">where</a>

  <a id="even.zero"></a><a id="21658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21658" class="InductiveConstructor">zero</a> <a id="21663" class="Symbol">:</a>
      <a id="21671" class="Comment">---------</a>
      <a id="21687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21603" class="Datatype">even</a> <a id="21692" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="21700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21700" class="InductiveConstructor">suc</a>  <a id="21705" class="Symbol">:</a> <a id="21707" class="Symbol">∀</a> <a id="21709" class="Symbol">{</a><a id="21710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21710" class="Bound">n</a> <a id="21712" class="Symbol">:</a> <a id="21714" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21715" class="Symbol">}</a>
    <a id="21721" class="Symbol">→</a> <a id="21723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21623" class="Datatype">odd</a> <a id="21727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21710" class="Bound">n</a>
      <a id="21735" class="Comment">------------</a>
    <a id="21752" class="Symbol">→</a> <a id="21754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21603" class="Datatype">even</a> <a id="21759" class="Symbol">(</a><a id="21760" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21710" class="Bound">n</a><a id="21765" class="Symbol">)</a>

<a id="21768" class="Keyword">data</a> <a id="21773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21623" class="Datatype">odd</a> <a id="21777" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="21786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21786" class="InductiveConstructor">suc</a>   <a id="21792" class="Symbol">:</a> <a id="21794" class="Symbol">∀</a> <a id="21796" class="Symbol">{</a><a id="21797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21797" class="Bound">n</a> <a id="21799" class="Symbol">:</a> <a id="21801" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21802" class="Symbol">}</a>
    <a id="21808" class="Symbol">→</a> <a id="21810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21603" class="Datatype">even</a> <a id="21815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21797" class="Bound">n</a>
      <a id="21823" class="Comment">-----------</a>
    <a id="21839" class="Symbol">→</a> <a id="21841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21623" class="Datatype">odd</a> <a id="21845" class="Symbol">(</a><a id="21846" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21797" class="Bound">n</a><a id="21851" class="Symbol">)</a>
</pre>{% endraw %}A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even:
{% raw %}<pre class="Agda"><a id="e+e≡e"></a><a id="23011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23011" class="Function">e+e≡e</a> <a id="23017" class="Symbol">:</a> <a id="23019" class="Symbol">∀</a> <a id="23021" class="Symbol">{</a><a id="23022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23022" class="Bound">m</a> <a id="23024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23024" class="Bound">n</a> <a id="23026" class="Symbol">:</a> <a id="23028" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="23029" class="Symbol">}</a>
  <a id="23033" class="Symbol">→</a> <a id="23035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21603" class="Datatype">even</a> <a id="23040" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23022" class="Bound">m</a>
  <a id="23044" class="Symbol">→</a> <a id="23046" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21603" class="Datatype">even</a> <a id="23051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23024" class="Bound">n</a>
    <a id="23057" class="Comment">------------</a>
  <a id="23072" class="Symbol">→</a> <a id="23074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21603" class="Datatype">even</a> <a id="23079" class="Symbol">(</a><a id="23080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23022" class="Bound">m</a> <a id="23082" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23024" class="Bound">n</a><a id="23085" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="23088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23088" class="Function">o+e≡o</a> <a id="23094" class="Symbol">:</a> <a id="23096" class="Symbol">∀</a> <a id="23098" class="Symbol">{</a><a id="23099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23099" class="Bound">m</a> <a id="23101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23101" class="Bound">n</a> <a id="23103" class="Symbol">:</a> <a id="23105" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="23106" class="Symbol">}</a>
  <a id="23110" class="Symbol">→</a> <a id="23112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21623" class="Datatype">odd</a> <a id="23116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23099" class="Bound">m</a>
  <a id="23120" class="Symbol">→</a> <a id="23122" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21603" class="Datatype">even</a> <a id="23127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23101" class="Bound">n</a>
    <a id="23133" class="Comment">-----------</a>
  <a id="23147" class="Symbol">→</a> <a id="23149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21623" class="Datatype">odd</a> <a id="23153" class="Symbol">(</a><a id="23154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23099" class="Bound">m</a> <a id="23156" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23101" class="Bound">n</a><a id="23159" class="Symbol">)</a>

<a id="23162" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23011" class="Function">e+e≡e</a> <a id="23168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21658" class="InductiveConstructor">zero</a>     <a id="23177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23177" class="Bound">en</a>  <a id="23181" class="Symbol">=</a>  <a id="23184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23177" class="Bound">en</a>
<a id="23187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23011" class="Function">e+e≡e</a> <a id="23193" class="Symbol">(</a><a id="23194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21700" class="InductiveConstructor">suc</a> <a id="23198" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23198" class="Bound">om</a><a id="23200" class="Symbol">)</a> <a id="23202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23202" class="Bound">en</a>  <a id="23206" class="Symbol">=</a>  <a id="23209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21700" class="InductiveConstructor">suc</a> <a id="23213" class="Symbol">(</a><a id="23214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23088" class="Function">o+e≡o</a> <a id="23220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23198" class="Bound">om</a> <a id="23223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23202" class="Bound">en</a><a id="23225" class="Symbol">)</a>

<a id="23228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23088" class="Function">o+e≡o</a> <a id="23234" class="Symbol">(</a><a id="23235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21786" class="InductiveConstructor">suc</a> <a id="23239" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23239" class="Bound">em</a><a id="23241" class="Symbol">)</a> <a id="23243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23243" class="Bound">en</a>  <a id="23247" class="Symbol">=</a>  <a id="23250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#21786" class="InductiveConstructor">suc</a> <a id="23254" class="Symbol">(</a><a id="23255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23011" class="Function">e+e≡e</a> <a id="23261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23239" class="Bound">em</a> <a id="23264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Relations.md %}{% raw %}#23243" class="Bound">en</a><a id="23266" class="Symbol">)</a>
</pre>{% endraw %}Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.

To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

{% raw %}<pre class="Agda"><a id="24404" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin]({{ site.baseurl }}/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    ⟨⟩ I O I I
    ⟨⟩ O O I O I I

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can b
    ------------
    Can (inc b)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can b
    ---------------
    to (from b) ≡ b

(Hint: For each of these, you may first need to prove related
properties of `One`. Also, you may need to prove that
if `One b` then `1` is less or equal to the result of `from b`.)

{% raw %}<pre class="Agda"><a id="25781" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Standard library

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="25917" class="Keyword">import</a> <a id="25924" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="25933" class="Keyword">using</a> <a id="25939" class="Symbol">(</a><a id="25940" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="25943" class="Symbol">;</a> <a id="25945" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="25948" class="Symbol">;</a> <a id="25950" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="25953" class="Symbol">)</a>
<a id="25955" class="Keyword">import</a> <a id="25962" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="25982" class="Keyword">using</a> <a id="25988" class="Symbol">(</a><a id="25989" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="25995" class="Symbol">;</a> <a id="25997" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="26004" class="Symbol">;</a> <a id="26006" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="26015" class="Symbol">;</a> <a id="26017" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="26024" class="Symbol">;</a>
                                  <a id="26060" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="26069" class="Symbol">;</a> <a id="26071" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="26080" class="Symbol">;</a> <a id="26082" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="26090" class="Symbol">)</a>
</pre>{% endraw %}In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives]({{ site.baseurl }}/Connectives/)),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.


## Unicode

This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
