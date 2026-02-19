#!/usr/bin/env bash

echo "Cleaning result of extraction"

if [ ! -d "extraction" ]
then
    mkdir extraction
fi

shopt -s nullglob # make the for loop do nothnig when there is no *.ml* files

echo "Done cleaning"

files=`cat template.files`

if [[ ! -f "verified_extraction_plugin.cmxs" ||
           "verified_extraction_plugin.cmxs" -ot "../theories/Extraction.vo" ]]
then
    cd extraction
    # Move extracted modules to build the plugin
    # Uncapitalize modules to circumvent a bug of coqdep with mllib files
    for i in *.ml*
      do
      newi=`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
      if [ $i != $newi ]
      then
          # echo "Moving " $i "to" $newi;
          mv $i tmp;
          mv tmp $newi;
      fi
    done
    cd ..

    # Remove extracted modules already linked in template_coq_plugin, checker and pcuic.
    echo "Removing:" $files
    rm -f $files
else
    echo "Extraction up-to date"
fi

# Extraction bug: opens are in the wrong order
OUT="$(patch -p0 --forward < fix_extraction.patch)" || echo "${OUT}" | grep "Skipping patch" -q || (echo "$OUT" && false);
# patch -N -p0 < fix_extraction.patch || exit $?
# patch -N -p0 < fix_extraction2.patch || exit $?
# patch -N -p0 < fix_extraction3.patch || exit $?
exit 0
