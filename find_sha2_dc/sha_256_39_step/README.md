#sha_256_39_step

1> Using the find_dc_msg_model.py to find the minimal value of expanded message words (0-38). In this steps,we need only obtain the minimal HW value of expanded message words.

2> Add the minimum HW value of the expanded message words to the find_dc_model.py to find the differential characteristic (0-38 step).

3> the varify_dc_model.py to verify the differential characteristic.

4> read_dc_solution.py to read the solution from find_dc_msg_model and find_dc_model.py.
   In the read_dc_solution, we need change "XXXXX.out" from find_dc_msg_model and find_dc_model.py.

5> read_varify_solution.py to read the solution from varify_dc_model.py.