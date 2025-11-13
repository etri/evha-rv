database -open waves -into waves.shm -default
#probe -create -shm [scope -tops] -all -depth to_cells -packed 16384
probe -create -shm [scope -tops] -all -memories -depth all -packed 16384 -unpacked 1024
run 
