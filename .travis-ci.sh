#!/usr/bin/env bash

set -ev

eval $(opam config env)

opam update

opam pin add caspertoychain . --yes --verbose
