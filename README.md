
This is stuff I did as a master student to help me understand set
theory and Coq at the same time. This was around 2012-2013.

Given the timing it's probably compatible with Coq 8.4 or maybe 8.3, I
don't have either at hand to test.

I started from someone else's development and played with it as I
liked. I didn't write down where I got it from, but since the
shortened tactics (`ir` for `intros`, `ap` for `apply`, etc) and some
lemma names survived my changes we can tell it was probably
https://github.com/coq-contribs/cats-in-zfc (original author Carlos
Simpson, see also paper https://arxiv.org/abs/math/0410224 and
https://math.unice.fr/~carlos/old/indexFev07.html which has history
from before the svn to git import). LICENSE is accordingly LGPL2.1.

Some differences:

- cats-in-zfc has a mix of axiomatic ZFC and using Coq types as sets,
  i.e. they have `Definition E := Type.` and then some extra axioms on
  `E`. I have purely axiomatic `E` with Coq serving as the metatheory.

- cats-in-zfc have some stuff in their notation.v to embed methods in
  their sets or something. I didn't understand it back then (and
  remember even less now) so I removed it and refactored or removed
  its users. (the previous point may not have been possible without
  this change by the way)

- as indicated by the name cats-in-zfc is about categories. I didn't
  know or care about categories so I deleted those files. Instead I
  have some trivialities about numbers in set theory.

- probably some other stuff that I forgot about.
