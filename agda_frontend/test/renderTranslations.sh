#!/bin/zsh

# PREREQUISITES:
#   - generated target files are placed under dist/
BUILD_DIR=dist
#   - Agda generated HTML is placed under html/
AGDA_HTML_DIR=html

echo "Rendering translations..."

for f in $BUILD_DIR/**/**; do

  echo " * $f"
  ext=${f##*.}
  fn=${${f#"$BUILD_DIR"/}%."$ext"}

  mdFn="$f".md
  lang=$(case $ext in
    "ast") echo "";;
    "txt") echo "";;
    "v") echo "coq";; # alas, pandoc has no coq/rocq syntax-highlighting support
    *) echo "";;
  esac)
  echo "\`\`\`$lang" > $mdFn
  cat $f >> $mdFn
  echo "\`\`\`" >> $mdFn

  targetHtml="$f".html
  pandoc --quiet -i "$mdFn" -o "$targetHtml" --highlight-style=tango
done

mkdir -p "$AGDA_HTML_DIR/$BUILD_DIR"
cp $BUILD_DIR/*.html "$AGDA_HTML_DIR/$BUILD_DIR"

for f in $BUILD_DIR/**/**.txt; do

  ext=${f##*.}
  fn=${${f#"$BUILD_DIR"/}%."$ext"}

  fTxt="$f"
  fAst="$BUILD_DIR"/"$fn".ast
  fCoq="$BUILD_DIR"/"$fn".v

  sourceHtml=$AGDA_HTML_DIR/$(echo $fn | tr '/' '.').html
  [ ! -f $sourceHtml ] && \
    echo " No corresponding HTML for $f (should be at $sourceHtml)" && \
    exit 1
  echo " * $sourceHtml"
  sed -i "s%class=\"Agda\"%class=\"split left Agda\"%g" $sourceHtml
  newHtml="\
<div class=\"split right\">\
<div class=\"tabs\">\
    <span data-tab-value=\"#tab_1\">Debug</span>\
    <span data-tab-value=\"#tab_2\">λ\&\#9744;</span>\
    <span data-tab-value=\"#tab_3\">Rocq</span>\
</div>\
<div class=\"tab-content\">\
    <div class=\"tabs__tab active\" id=\"tab_1\" data-tab-info>\
        <embed src=\"$fTxt.html\"/>\
    </div>\
    <div class=\"tabs__tab\" id=\"tab_2\" data-tab-info>\
        <embed src=\"$fAst.html\"/>\
    </div>\
    <div class=\"tabs__tab\" id=\"tab_3\" data-tab-info>\
        <embed src=\"$fCoq.html\"/>\
    </div>\
</div>\
</div>\
<script type="text/javascript">\
  document.querySelectorAll('[data-tab-value]').forEach(tab => {tab.addEventListener('click', () => {\
    document.querySelectorAll('[data-tab-info]').forEach(tabInfo => {tabInfo.classList.remove('active') });\
    document.querySelector(tab.dataset.tabValue).classList.add('active');\
  })})\
</script>"
  sed -i "s%</body>%$newHtml</body>%g" $sourceHtml
done

echo "...done!"
