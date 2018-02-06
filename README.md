# qoc
Quantum Over Coq

Coq library that implements quantum computing.

## Running

In order to run this, you will need the development version of the Mathematical
Components library available [here](http://github.com/math-comp/math-comp) (the
released version does not include the complex number module).

Then, run Coq (or CoqIDE) with the following arguments:
`-R <path>/math-comp/mathcomp mathcomp -R . quantum`
(where `<path>` is the path to the Mathema)ical Components Library)
