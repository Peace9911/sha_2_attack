#sha_256_31_step

1> Using the find_dc_msg_model.py to find the minimal value of expanded message words (0-30). In this steps,we need obtain the differential characteristic of expanded message words. 

2> Add the extended message words that correspond to the constraints to the find_dc_model.py file. Then, Using the find_dc_model.py to find the differential characteristic (0-31 step).

3> Use the correct_dc_model.py to correct the differential characteristics from find_dc_model.py.

3> the varify_dc_model.py to verify the differential characteristic from correct_dc_model.py.

4> read_dc_solution.py to read the solution from find_dc_msg_model, find_dc_model.py and correct_dc_model.py.
   In read_dc_solution, we need change "XXXXX.out" from find_dc_msg_model, find_dc_model.py and correct_dc_model.py

5> read_varify_solution.py to read the solution from varify_dc_model.py.