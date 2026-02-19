#!/bin/bash

RUST_PATH=./extracted-code/rust/
RUST_SUFFIX_PATH=extracted/src/
RUST_SUFFIX=extracted/src/main.rs

rust_examples="BernsteinYangTermination Ack Even"
echo "Processing Rust extraction"
for f in ${rust_examples}
do
    if [[ ! -e "$RUST_PATH/${f}.rs.out" ]]; then continue; fi
    mkdir -p $RUST_PATH/${f}-${RUST_SUFFIX_PATH}
    src_rust_fname=$RUST_PATH/${f}.rs.out
    tgt_rust_fname=$RUST_PATH/${f}-${RUST_SUFFIX}
    main_rust_name=$RUST_PATH/${f}.main
    echo "removing previous extraction: " ${tgt_rust_fname}
    rm -f ${tgt_rust_fname}
    echo Processing $src_rust_fname "--->" $tgt_rust_fname
    cat $src_rust_fname $main_rust_name | sed "/^Debug/d" > $tgt_rust_fname
done

ELM_PATH=./extracted-code/elm/elm-extract
ELM_WEB_PATH=./extracted-code/elm/elm-web-extract
ELM_TESTS=$ELM_PATH/tests
ELM_WEB_SRC=$ELM_WEB_PATH/src

echo "Processing Elm extraction"
for f in $ELM_PATH/*.elm.out;
do
    if [[ ! -e "$f" ]]; then continue; fi
    echo $f "--->" $ELM_TESTS/$(basename ${f%.out}) ;
    sed -n 's/ *"//;/module/,/suite/p' $f > $ELM_TESTS/$(basename ${f%.out})
done

WEB_APP_OUT=UserList.elm.out

echo "Processing Elm web-app extraction"
echo $WEB_APP_OUT "+ views.elm"  "--->" $ELM_WEB_SRC/Main.elm;
cat $ELM_WEB_PATH/$WEB_APP_OUT $ELM_WEB_SRC/views.elm > $ELM_WEB_SRC/Main.elm
