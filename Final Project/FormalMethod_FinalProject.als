module SnappFoodDelivery

-- sig customer { ordering: order -> food -> restaurant -> restaurantAdmin -> driver }
-- sig delivery   { submiting: order -> payment -> transactionReports -> administrator }
-- sig food        { access: subCategory -> category }

sig Customer {
	has: some Order
	}

sig Order {
	belongsTo: one (Delivery + Customer),
	has: some Food,
	makes: some Payment
	}

sig Delivery {
	has: some Order
	}

sig Food {
has: one Category,
belongsTo: some Order,
madeIn: one Restaurant,
id: Id
	}

sig Category {
	belongsTo: one SubCategory
	}

sig SubCategory {
has: set Food,
belongsTo: one Category
	}

sig Bank {
	payment: some Payment
	}

sig Payment {
	belongsTo: one Order,
	makes: set TransactionReports,
	has: one Bank
	}

sig TransactionReports {
	belongsTo: one Payment,
	controlBy: some (Manager + Administrator)
	}

sig Manager {
controls: set TransactionReports,
member: some Administrator
}

sig Administrator {
controls: set TransactionReports,
headOf: set Manager,
id: one Id
}

sig Restaurant {
make: set Food,
has: some RestaurantAdmin
}

sig RestaurantAdmin {
belongsTo: one Restaurant,
commands: some Driver,
id: one Id 
}

sig Driver {
getInfoBy: some RestaurantAdmin,
id: one Id
}

sig Id {
blng: one Food
}

fact driver {
	all d1,d2: Driver | d1 != d2 => d1.id != d2.id
}

fact admin {
	all a1,a2: Administrator | a1 != a2 => a1.id != a2.id
        all r1,r2: RestaurantAdmin | r1 != r2 => r1.id != r2.id
}

assert Aadmin {
	all a1,a2: Administrator | a1 != a2 => a1.id != a2.id
        all r1,r2: RestaurantAdmin | r1 != r2 => r1.id != r2.id
	all d1,d2: Driver | d1 != d2 => d1.id != d2.id
}

fun FoodInfo (i:Id,f:Food) : (set Food) {
f.id.*blng
}

pred show [i:Id,f:Food] {
f in FoodInfo [i,f]
}

run show
check Aadmin


