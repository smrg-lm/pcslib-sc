// pcslib-sc 2011
// Combinatory Matrix

PCSMatrix {
	var <type;
	var <matrix;
	var <vnorm, <hnorm;

	*roman { arg norm;
		^super.new.initMatrix(norm, nil, \roman);
	}

	*t1a { arg norm;
		^super.new.initMatrix(norm, nil, \t1a);
	}

	*t1b { arg norm;
		^super.new.initMatrix(norm, nil, \t1b);
	}

	*t2 { arg hnorm, vnorm;
		^super.new.initMatrix(hnorm, vnorm, \t2);
	}

	initMatrix { arg hn, vn, t;
		matrix = [];
		type = t;

		if(hn.class == PCS, {
			hn = hn.asArray.clump(1).collect({ arg i; i.as(PCS) });
		});
		if(vn.class == PCS, {
			vn = vn.asArray.clump(1).collect({ arg i; i.as(PCS) });
		});

		switch(type,
			\roman, {
				hnorm = vnorm = hn;
				matrix = hnorm.size.collect({ arg i;
					hnorm.rotate(i.neg);
				});
			},
			\t1a, {
				hnorm = vnorm = hn;
				matrix = hnorm.collect({ arg i;
					hnorm.collect({ arg j;
						(j.asArray + i.asArray).as(PCS);
					});
				});
			},
			\t1b, {
				hnorm = vnorm = hn;
				matrix = hnorm.collect({ arg i;
					hnorm.collect({ arg j;
						(j.asArray + i.i.asArray).as(PCS);
					});
				});
			},
			\t2, {
				hnorm = hn;
				vnorm = vn ? hn;
				matrix = vnorm.collect({ arg i;
					hnorm.collect({ arg j;
						(j.asArray + i.asArray).as(PCS);
					});
				});
			}
		);
	}

	/* from Matrix
	printOn { arg stream;
		if (stream.atLimit) { ^this };
		stream << this.class.name << "[ " ;
		matrix.do({ arg row, i;
			if (stream.atLimit) { ^this };
			if (i != 0, { stream.comma; });
			stream << "\n";
			stream.tab;
			row.printOn(stream);
		});
		stream << "\n";
		stream << " ]" ;
	}
	*/
}

