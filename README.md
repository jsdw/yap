# YAP: Yet Another (rust) Parser library

A lightweight, dependency free, parser combinator inspired set of utility methods to help with parsing input.

The goal of YAP is to provide a lightweight, easy to understand interface that exposes common, parser combinator style
methods to make it easy to parse things (currently strings and slices, but it can be user-extended to other types), but
also ensure that errors can be easily created and propagated, and things like location information are readily accessible.

