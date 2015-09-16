# @ job_name = MSP_kl291649_1000x1000
# @ account_no = G52-5
# @ class = kdm-dev
# @ error = MSP_kl291649_1000x1000.err
# @ output = MSP_kl291649_1000x1000.out
# @ environment = COPY_ALL
# @ wall_clock_limit = 00:20:00
# @ notification = error
# @ notify_user = kl291649@icm.edu.pl
# @ job_type = bluegene
# @ bg_size = 2
# @ queue
echo "Started at" `date`
mpirun -np 32 -mode VN msp-par.exe 1000 1000 123
echo "Finished at" `date`
