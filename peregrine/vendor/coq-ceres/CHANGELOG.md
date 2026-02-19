# 0.4.1

- Build with Dune
- Compatibility with 8.14, 8.15, 8.16, 8.17

# 0.4.0

- Reexport `CeresParser` and `CeresFormat` in `Ceres`
- Add `CeresParserUtils` and `CeresParserInternal`
- Rename `string_of_sexp` to `string_of_sexp_`
- Rename `string_of_sexpa` to `string_of_sexp`

# 0.3.0

- Add `Serialize` and `Deserialize` instances for `ascii`
- Prove roundtrip properties

    + Parser (string -> sexp): parse-then-print roundtrip (soundness; see `CeresParserRoundtrip`)
    + Serializers (sexp <-> mytype): both ways (see `CeresRoundtrip`, exported by default)

- The concrete syntax becomes stricter. Strings must consist of printable characters
  (only `\\` and `\n` are currently supported escape sequences), and atoms
  (identifiers) have a restricted alphabet:

  ```
  is_alphanum c ||| string_elem c "'=-+*/:!?@#$%^&_<>~|.,"
  ```

# 0.2.0

- Add decidable equality

# 0.1.0

- Create coq-ceres.
