match Test_add.malfunction_Plugin_tests_test_extract_test_add with
| Test_add.S _ -> Printf.printf "ok\n"
| Test_add.O -> Printf.printf "error\n";;


