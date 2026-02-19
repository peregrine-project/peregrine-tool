#!/usr/bin/env bash

if [[ ! -f "src/rust_extraction_plugin.cmxs" ||
      "src/rust_extraction_plugin.cmxs" -ot "theories/ExtractExtraction.vo" ]]
then
  cd src
  # Uncapitalize modules to circumvent a bug of rocqdep with mlpack files
  for i in *.ml*
  do
    newi=`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
    tmp="${i}.tmp"
    if [ $i != $newi ]
    then
      echo "Moving " $i "to" $newi;
      # Move in two steps to circumvent a bug on case insensitive file systems
      mv $i $tmp;
      mv $tmp $newi;
    fi
  done

  # This file was generated with
  # cat template-rocq/_PluginProject | grep "^[^#].*mli\?$" | sed "s/gen-src\///"
  # from MetaRocq root
  files=`cat ../template-rocq-files.txt`
  echo "Removing files linked in template-rocq:" $files
  rm -f $files
else
  echo "Extraction up to date"
fi
