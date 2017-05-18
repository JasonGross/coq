#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

fiat_crypto_CI_DIR=${CI_BUILD_DIR}/fiat-crypto

git_checkout --recursive ${fiat_crypto_CI_BRANCH} ${fiat_crypto_CI_GITURL} ${fiat_crypto_CI_DIR}

( cd ${fiat_crypto_CI_DIR} && ./etc/coq-scripts/timing/make-pretty-timed.sh -j ${NJOBS} lite && make -j ${NJOBS} lite )
