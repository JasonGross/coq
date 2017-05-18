#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

fiat_parsers_CI_DIR=${CI_BUILD_DIR}/fiat

git_checkout --recursive ${fiat_parsers_CI_BRANCH} ${fiat_parsers_CI_GITURL} ${fiat_parsers_CI_DIR}

( cd ${fiat_parsers_CI_DIR} && ./etc/coq-scripts/timing/make-pretty-timed.sh -j ${NJOBS} parsers && make -j ${NJOBS} parsers )
