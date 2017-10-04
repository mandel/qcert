import { Success, Failure, Error, Request, Response} from "./types";
import { Credentials, DeployIn, DeployOut, Design, Designs } from "./types";
import openwhisk = require("openwhisk");

export type ListIn = Credentials & DeployIn
export type ListOut = Credentials & DeployOut

const main = async (params:ListIn) : Promise<ListIn> => {
    const pkgname: string = params.pkgname;
    const designs: Designs = params.querycode;
    const ow = openwhisk()

    // Delete dbcopies
    await Promise.all(designs.designs.map(async (design:Design) => {
	const dbname: string = design.dbname
	const views = design.design.views
	var dbcopies = []
	for (var key in views) {
	    if (views.hasOwnProperty(key)) {
		dbcopies.push(views[key].dbcopy);
	    }
	}
	
	const dbcopy = views.dbcopy
	await Promise.all(dbcopies.map(async (dbcopy) => {
            try {
		await ow.actions.invoke({
		    name: "/whisk.system/cloudant/delete-database",
		    blocking: true,
		    params: {
			host: `${params.cloudant.username}.cloudant.com`,
			username: `${params.cloudant.username}`,
			password: `${params.cloudant.password}`,
			dbname: dbcopy
		    }
		})
            } catch (err) {
		console.log('Unable to delete database:'+dbname+' with error:'+err);
            }
	}))	
    }))
    // Delete initial database view
    let firstDesign: Design
    try {
	firstDesign = designs.designs[0]
    } catch (error) {
	console.error("Should have at least one design document")
    }
    const viewname = '_design/'+pkgname
    try {
        const entry =
            await ow.actions.invoke({
                name: "/whisk.system/cloudant/read",
                blocking: true,
                params: {
                    host: `${params.cloudant.username}.cloudant.com`,
                    username: `${params.cloudant.username}`,
                    password: `${params.cloudant.password}`,
                    docid: viewname,
                    dbname: firstDesign.dbname
                }
            })
        await ow.actions.invoke({
	    name: "/whisk.system/cloudant/delete-document",
	    blocking: true,
	    params: {
                host: `${params.cloudant.username}.cloudant.com`,
                username: `${params.cloudant.username}`,
                password: `${params.cloudant.password}`,
		docid: viewname, docrev: entry.response.result._rev,
                dbname: firstDesign.dbname
	    }
        })
    } catch (err) {
        console.log('Unable to delete view '+viewname+' in database:'+firstDesign.dbname+' with error:'+err)
    }
    return params;
}

const failure = (statusCode: Failure, err): Response<ListOut> => {
    return { error: { message: err, statusCode: statusCode } }
}
