# nargo check --overwrite
time nargo execute my_witness
bb write_vk -b ./target/merkle_tree_gen.json -o ./target
# /usr/bin/time -v bb prove -vb target/merkle_tree_gen.json -w target/my_witness.gz -o proof
/usr/bin/time -v bb prove -vb target/merkle_tree_gen.json -w target/my_witness.gz -o target
time bb verify -k target/vk -p target/proof